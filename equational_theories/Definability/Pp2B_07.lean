import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyx_y_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq21 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq9
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq9
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq43
    | exact resolve eq43 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1 (M.op X0 X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq43
    | exact resolve eq43 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq362 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq365 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq362 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq362
    | (have j0 := eq362 (σ X0) (σ X1)
       grind)
    | exact resolve eq362 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq362 X1 (τ X0)
       grind)
    | exact superpose eq362 eq18
    | (have j1 := eq362 X1 (τ X0)
       grind)
    | exact resolve eq18 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq365 y x
       grind)
    | exact superpose eq365 eq16
    | (have j1 := eq365 y x
       grind)
    | exact resolve eq16 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 (σ X0)
       have i₂ := eq365 X0 X0
       grind)
    | exact superpose eq365 eq32
    | (have j1 := eq365 X0 (k X0 X0)
       grind)
    | exact resolve eq32 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq464 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X1 (M.op X0 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87 (M.op X1 (M.op X0 X2)) (M.op X0 X0) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq87
    | exact resolve eq87 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq595 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 (M.op X0 X1) X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq464
    | exact resolve eq464 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq634 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq595 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq595
    | exact resolve eq595 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq595
  have eq5322 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq381 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq381
    | exact resolve eq381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq5359 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5322 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5322
    | (have j0 := eq5322 X0 X1
       grind)
    | exact resolve eq5322 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5322
  have eq6248 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq405
       have i₂ := eq362 y x
       grind)
    | exact superpose eq362 eq405
    | (have j1 := eq362 (σ y) (σ x)
       grind)
    | exact resolve eq405 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6251 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq6248
  have eq6261 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq88 (σ x) (σ y)
       have i₂ := eq6251
       grind)
    | exact superpose eq6251 eq88
    | exact resolve eq88 eq6251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6945 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6251
       have i₂ := eq6261
       grind)
    | exact superpose eq6261 eq6251
    | exact resolve eq6251 eq6261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6251 eq6261
  have eq7003 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq6945
  have eq7018 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq32 (σ x)
       have i₂ := eq7003
       grind)
    | exact superpose eq7003 eq32
    | exact resolve eq32 eq7003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7106 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7018
       grind)
    | exact superpose eq7018 eq16
    | exact resolve eq16 eq7018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7018
  have eq7476 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq415 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq415
    | (have j0 := eq415 (τ X0)
       grind)
    | exact resolve eq415 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq7549 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7476 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7476
    | (have j0 := eq7476 X0
       grind)
    | exact resolve eq7476 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7476
  have eq7554 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7549 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7549
    | (have j0 := eq7549 X0
       grind)
    | exact resolve eq7549 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7549
  have eq7584 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq634 (k X0 X0) X0
       have i₂ := eq7554 X0
       grind)
    | exact superpose eq7554 eq634
    | (have j1 := eq7554 X0
       grind)
    | exact resolve eq634 eq7554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634 eq7554
  have eq7886 : ∀ X0 : G, (M.op X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 (k X0 X0) X0
       have i₂ := eq7584 X0
       grind)
    | exact superpose eq7584 eq13
    | (have j0 := eq13 (k X0 X0) X0
       have j1 := eq7584 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq7584 X0
       grind)
    | exact resolve eq13 eq7584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7584
  have eq7976 : ∀ X0 : G, (M.op X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7886 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7886
  have eq7983 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7976 X0
       have j1 := eq362 X0 X0
       grind)
    | (have r₁ := eq7976 X0
       have r₂ := eq362 X0 X0
       grind)
    | exact resolve eq7976 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7976
  have eq8005 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (k (τ X0) (τ X0))
       have i₂ := eq7983 (τ X0)
       grind)
    | exact superpose eq7983 eq18
    | (have j1 := eq7983 (τ X0)
       grind)
    | exact resolve eq18 eq7983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7983
  have eq8007 : ∀ X0 : G, (σ (τ X0)) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq8005 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq8005
    | (have j0 := eq8005 X0
       grind)
    | exact resolve eq8005 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq8005
  have eq8024 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8007 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8007
    | (have j0 := eq8007 X0
       grind)
    | exact resolve eq8007 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8007
  have eq9105 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq41 (τ X0) X1
       have i₂ := eq8024 X0
       grind)
    | exact superpose eq8024 eq41
    | (have j1 := eq8024 X0
       grind)
    | (have r₁ := eq41 (τ X0) X1
       have r₂ := eq8024 X0
       grind)
    | exact resolve eq41 eq8024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq8024
  have eq9168 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq9105 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9105
  have eq17708 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ X0) = (k (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9168 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9168
    | (have j0 := eq9168 (σ X0) X1
       grind)
    | exact resolve eq9168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9168
  have eq17806 : ∀ X0 X1 : G, (σ X0) = (σ (k (k (τ (σ X0)) X0) X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17708 X0 X1
       have i₂ := eq21 (σ X0) X0 X0
       grind)
    | exact superpose eq21 eq17708
    | (have j0 := eq17708 X0 X1
       grind)
    | exact resolve eq17708 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq17708
  have eq17819 : ∀ X0 X1 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17806 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17806
    | (have j0 := eq17806 X0 X1
       grind)
    | exact resolve eq17806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17806
  have eq18120 : ∀ X0 X1 : G, (τ (σ X0)) = (k (k X0 X0) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (k X0 X0) X0)
       have i₂ := eq17819 X0 X1
       grind)
    | exact superpose eq17819 eq10
    | (have j1 := eq17819 X0 X1
       grind)
    | exact resolve eq10 eq17819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17819
  have eq18157 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18120 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18120
    | (have j0 := eq18120 X0 X1
       grind)
    | exact resolve eq18120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18120
  have eq18189 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18157 X0 X1
       have i₂ := eq362 X0 X0
       grind)
    | exact superpose eq362 eq18157
    | (have j0 := eq18157 X0 X1
       have j1 := eq362 X1 X0
       grind)
    | exact resolve eq18157 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq18157
  have eq18258 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq18189 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq18189 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq18189 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18189
  have eq18533 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq18258 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18258
  have eq18535 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq18533 X0
       grind)
    | (have r₁ := eq18533 X0
       have r₂ := eq32 X0
       grind)
    | exact resolve eq18533 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18533
  have eq18557 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18535 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq18535
    | exact resolve eq18535 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18535
  have eq18579 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18557 (σ x)
       have i₂ := eq7003
       grind)
    | exact superpose eq7003 eq18557
    | exact resolve eq18557 eq7003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7003
  have eq18626 : (σ x) = (σ (k y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18579
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq18579
    | exact resolve eq18579 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18579
  have eq19474 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5359 x y
       have i₂ := eq18626
       grind)
    | exact superpose eq18626 eq5359
    | (have j0 := eq5359 x y
       grind)
    | exact resolve eq5359 eq18626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5359 eq18626
  have eq19500 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by grind
  clear eq19474
  have eq19517 : y = (M.op y x) := by
    first
    | (have r₁ := eq19500
       have r₂ := eq7106
       grind)
    | exact resolve eq19500 eq7106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7106 eq19500
  have eq19527 : (M.op y x) = (M.op x x) := by
    first
    | (have i₁ := eq88 x y
       have i₂ := eq19517
       grind)
    | exact superpose eq19517 eq88
    | exact resolve eq88 eq19517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19594 : y = (M.op x x) := by
    first
    | (have i₁ := eq19527
       have i₂ := eq19517
       grind)
    | exact superpose eq19517 eq19527
    | exact resolve eq19527 eq19517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19517 eq19527
  have eq19599 : x = (M.op x y) := by
    first
    | (have i₁ := eq32 x
       have i₂ := eq19594
       grind)
    | exact superpose eq19594 eq32
    | exact resolve eq32 eq19594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19628 : x = (k y x) := by
    first
    | (have i₁ := eq18557 x
       have i₂ := eq19594
       grind)
    | exact superpose eq19594 eq18557
    | exact resolve eq18557 eq19594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18557 eq19594
  have eq19809 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq405
       have i₂ := eq19628
       grind)
    | exact superpose eq19628 eq405
    | exact resolve eq405 eq19628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405 eq19628
  have eq19821 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq19809
       have i₂ := eq19599
       grind)
    | exact superpose eq19599 eq19809
    | exact resolve eq19809 eq19599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19809
  have eq19822 : (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq19821
  have eq20390 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq88 (σ x) (σ y)
       have i₂ := eq19822
       grind)
    | exact superpose eq19822 eq88
    | exact resolve eq88 eq19822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq20459 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20390
       have i₂ := eq19822
       grind)
    | exact superpose eq19822 eq20390
    | exact resolve eq20390 eq19822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19822 eq20390
  have eq20547 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32 (σ x)
       have i₂ := eq20459
       grind)
    | exact superpose eq20459 eq32
    | exact resolve eq32 eq20459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq20459
  have eq20684 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20547
       grind)
    | exact superpose eq20547 eq16
    | exact resolve eq16 eq20547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20547
  have eq20785 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq20684
       have i₂ := eq19599
       grind)
    | exact superpose eq19599 eq20684
    | exact resolve eq20684 eq19599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19599 eq20684
  have eq20786 : False := by grind
  exact eq20786

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pyy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq62
    | exact resolve eq62 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq62
  have eq348 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq349 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq348 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq348
    | (have j0 := eq348 (σ X0) (σ X1)
       grind)
    | exact resolve eq348 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq348 X1 (τ X0)
       grind)
    | exact superpose eq348 eq18
    | (have j1 := eq348 X1 (τ X0)
       grind)
    | exact resolve eq18 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq367 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq348 (τ X1) X0
       grind)
    | exact superpose eq348 eq17
    | (have j1 := eq348 (τ X1) X0
       grind)
    | exact resolve eq17 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq443 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq349 y x
       grind)
    | exact superpose eq349 eq16
    | (have j1 := eq349 y x
       grind)
    | exact resolve eq16 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq349 X0 X0
       grind)
    | exact superpose eq349 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq349 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq349 X1 X1
       grind)
    | exact resolve eq12 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq459 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq452 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq452 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq452 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq514 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X1 (M.op X0 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87 (M.op X1 (M.op X0 X2)) (M.op X0 X0) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq87
    | exact resolve eq87 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq643 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq514 X0 (M.op X0 X1) X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq514
    | exact resolve eq514 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq1404 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq356 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq52 (τ X0)
       grind)
    | exact superpose eq52 eq356
    | (have j0 := eq356 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact resolve eq356 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq1427 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1404 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1404
    | (have j0 := eq1404 X0
       grind)
    | exact resolve eq1404 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq1429 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1427 X0
       have i₂ := eq88 (τ X0) (τ X0)
       grind)
    | exact superpose eq88 eq1427
    | (have j0 := eq1427 X0
       grind)
    | exact resolve eq1427 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq1427
  have eq2075 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq443
       have i₂ := eq348 y x
       grind)
    | exact superpose eq348 eq443
    | (have j1 := eq348 (σ y) (σ x)
       grind)
    | exact resolve eq443 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq2078 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq2075
  have eq2081 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (σ y))) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) X0 (σ x)
       have i₂ := eq2078
       grind)
    | exact superpose eq2078 eq9
    | exact resolve eq9 eq2078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11537 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1429 X0
       have i₂ := eq367 (τ X0) X0
       grind)
    | exact superpose eq367 eq1429
    | (have j0 := eq1429 X0
       have j1 := eq367 (τ X0) X0
       grind)
    | exact resolve eq1429 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq1429
  have eq11563 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq11537 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11537
  have eq11577 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11563 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11563
    | (have j0 := eq11563 X0
       grind)
    | exact resolve eq11563 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11563
  have eq11931 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq85 (τ X0) X1
       have i₂ := eq11577 X0
       grind)
    | exact superpose eq11577 eq85
    | (have j1 := eq11577 X0
       grind)
    | (have r₁ := eq85 (τ X0) X1
       have r₂ := eq11577 X0
       grind)
    | exact resolve eq85 eq11577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11577
  have eq11996 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11931 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11931
  have eq12815 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ X0) = (k (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11996 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11996
    | (have j0 := eq11996 (σ X0) X1
       grind)
    | exact resolve eq11996 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11996
  have eq12898 : ∀ X0 X1 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12815 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq12815
    | (have j0 := eq12815 X0 X1
       grind)
    | exact resolve eq12815 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12815
  have eq12906 : ∀ X0 X1 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12898 X0 X1
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq12898
    | (have j0 := eq12898 X0 X1
       grind)
    | exact resolve eq12898 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12898
  have eq13124 : ∀ X0 X1 : G, (τ (σ X0)) = (k (k X0 X0) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (k X0 X0) X0)
       have i₂ := eq12906 X0 X1
       grind)
    | exact superpose eq12906 eq10
    | (have j1 := eq12906 X0 X1
       grind)
    | exact resolve eq10 eq12906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12906
  have eq13157 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13124 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13124
    | (have j0 := eq13124 X0 X1
       grind)
    | exact resolve eq13124 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13124
  have eq13178 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13157 X0 X1
       have i₂ := eq348 X0 X0
       grind)
    | exact superpose eq348 eq13157
    | (have j0 := eq13157 X0 X1
       have j1 := eq348 X1 X0
       grind)
    | exact resolve eq13157 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13157
  have eq13229 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13178 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq13178 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq13178 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13178
  have eq13421 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13229 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13229
  have eq13422 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13421 X0
       grind)
    | (have r₁ := eq13421 X0
       have r₂ := eq52 X0
       grind)
    | exact resolve eq13421 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13421
  have eq13442 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13422 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq13422
    | exact resolve eq13422 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq13422
  have eq13480 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq13442 (σ X0)
       grind)
    | exact superpose eq13442 eq22
    | exact resolve eq22 eq13442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq13496 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13480 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13480
    | exact resolve eq13480 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13480
  have eq110895 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2081 (σ y)
       have i₂ := eq2078
       grind)
    | exact superpose eq2078 eq2081
    | exact resolve eq2081 eq2078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081
  have eq111189 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op y x) := by grind
  clear eq110895
  have eq113205 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq643 (σ x) (M.op (σ y) (σ y))
       have i₂ := eq111189
       grind)
    | exact superpose eq111189 eq643
    | exact resolve eq643 eq111189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111189
  have eq113464 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2078
       have i₂ := eq113205
       grind)
    | exact superpose eq113205 eq2078
    | exact resolve eq2078 eq113205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078 eq113205
  have eq113645 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq113464
  have eq113686 : x = (k (τ (σ x)) x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq13496 x
       have i₂ := eq113645
       grind)
    | exact superpose eq113645 eq13496
    | exact resolve eq13496 eq113645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13496 eq113645
  have eq113961 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq113686
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq113686
    | exact resolve eq113686 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113686
  have eq114036 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq348 x x
       have i₂ := eq113961
       grind)
    | exact superpose eq113961 eq348
    | (have j0 := eq348 x x
       grind)
    | exact resolve eq348 eq113961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq113961
  have eq114071 : x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq114036
  have eq114105 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq114071
       grind)
    | exact superpose eq114071 eq9
    | exact resolve eq9 eq114071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120656 : y = (M.op x (M.op y y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq114105 y
       have i₂ := eq114071
       grind)
    | exact superpose eq114071 eq114105
    | exact resolve eq114105 eq114071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114105
  have eq120950 : y = (M.op x (M.op y y)) ∨ x = (M.op x x) := by grind
  clear eq120656
  have eq121182 : (M.op y x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq643 x (M.op y y)
       have i₂ := eq120950
       grind)
    | exact superpose eq120950 eq643
    | exact resolve eq643 eq120950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq120950
  have eq121435 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq114071
       have i₂ := eq121182
       grind)
    | exact superpose eq121182 eq114071
    | exact resolve eq114071 eq121182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114071 eq121182
  have eq121603 : x = (M.op x x) := by grind
  clear eq121435
  have eq121640 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq85 x x
       have i₂ := eq121603
       grind)
    | exact superpose eq121603 eq85
    | (have r₁ := eq85 x x
       have r₂ := eq121603
       grind)
    | exact resolve eq85 eq121603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq121661 : x = (k x x) := by
    first
    | (have i₁ := eq13442 x
       have i₂ := eq121603
       grind)
    | exact superpose eq121603 eq13442
    | exact resolve eq13442 eq121603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13442 eq121603
  have eq121831 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq121640 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121640
  have eq121908 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq459 x X0
       have i₂ := eq121661
       grind)
    | exact superpose eq121661 eq459
    | (have j0 := eq459 x X0
       grind)
    | exact resolve eq459 eq121661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459 eq121661
  have eq122020 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq121908 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121908
  have eq125825 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq122020 (σ X0)
       grind)
    | exact superpose eq122020 eq15
    | exact resolve eq15 eq122020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122020
  have eq125922 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq125825 X0
       have i₂ := eq121831 X0
       grind)
    | exact superpose eq121831 eq125825
    | exact resolve eq125825 eq121831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121831 eq125825
  have eq128411 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq125922 y
       grind)
    | exact superpose eq125922 eq16
    | (have r₁ := eq16
       have r₂ := eq125922 y
       grind)
    | exact resolve eq16 eq125922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125922
  have eq128688 : False := by grind
  exact eq128688

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_x_pyx_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq93 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq98 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq94
  have eq99 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq93
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
  have eq107 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq106
    | exact resolve eq106 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq251 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq58 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58
    | (have j0 := eq58 y x
       grind)
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 X0)
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X2
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq11 X1 (τ X0)
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 X1 (τ X0)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq690 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op X0 X0) X0 X1 X2
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 y x X0 X1
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X1 X0) X1 X2 (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 X2 (M.op X0 X1) X1
       have i₂ := eq58 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq58 eq55
    | exact resolve eq55 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq789 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq78
    | (have j0 := eq78 X0 X1
       grind)
    | exact resolve eq78 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq78
  have eq882 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq789 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq789
    | (have j0 := eq789 X0 x
       grind)
    | exact resolve eq789 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq4225 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq704 X0 X0 X1
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq704
    | exact resolve eq704 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4278 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq4225 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4225
    | (have j0 := eq4225 y x
       grind)
    | exact resolve eq4225 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4225
  have eq4508 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq700 (M.op y X0) X0
       have i₂ := eq58 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq58 eq700
    | exact resolve eq700 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq4712 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq707 X0 X0 X2 X3 X1
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq707
    | exact resolve eq707 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq5617 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | exact superpose eq29 eq358
    | exact resolve eq358 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq5659 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | exact superpose eq40 eq5617
    | (have j0 := eq5617 X0
       grind)
    | exact resolve eq5617 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5617
  have eq5827 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq882 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq882
    | (have j0 := eq882 y
       grind)
    | exact resolve eq882 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq5851 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5827
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq5827
    | exact resolve eq5827 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq5827
  have eq5871 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq5851
    | exact resolve eq5851 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5851
  have eq5884 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5871
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq5871
    | exact resolve eq5871 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq5871
  have eq7612 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq690 X0 X1 (M.op X0 X0)
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq690
    | exact resolve eq690 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq9367 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq706 (M.op X1 X2) X1 X2 (M.op X1 X2) x x
       have i₂ := eq56 (M.op X1 X2)
       grind)
    | exact superpose eq56 eq706
    | exact resolve eq706 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq17242 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq257 X1 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq704 X1 X0 X1
       grind)
    | exact superpose eq704 eq257
    | exact resolve eq257 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq24316 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4712 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq56 (M.op X0 X1)
       grind)
    | exact superpose eq56 eq4712
    | exact resolve eq4712 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4712
  have eq24534 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24316 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq24316
    | exact resolve eq24316 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25057 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X1 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq7612 X1 X0
       grind)
    | exact superpose eq7612 eq14
    | exact resolve eq14 eq7612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33686 : y = (M.op (M.op x y) (M.op y x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq251
       have i₂ := eq107
       grind)
    | exact superpose eq107 eq251
    | exact resolve eq251 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq251
  have eq35864 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq24534 X0 y
       have i₂ := eq4508 X0
       grind)
    | exact superpose eq4508 eq24534
    | exact resolve eq24534 eq4508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4508
  have eq35868 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7612 X0 X1
       have i₂ := eq24534 X0 X1
       grind)
    | exact superpose eq24534 eq7612
    | exact resolve eq7612 eq24534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38464 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq729 X0 X1 X2
       have i₂ := eq24534 X1 X0
       grind)
    | exact superpose eq24534 eq729
    | exact resolve eq729 eq24534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq38823 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38464 X0 (M.op (M.op X1 X0) (M.op X1 X0)) X2
       have i₂ := eq7612 X0 X1
       grind)
    | exact superpose eq7612 eq38464
    | exact resolve eq38464 eq7612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7612
  have eq38840 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38464 (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0)) X2
       have i₂ := eq704 X0 X1 X2
       grind)
    | exact superpose eq704 eq38464
    | exact resolve eq38464 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq39221 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35868 X2 X1
       have i₂ := eq38464 X1 X2 X0
       grind)
    | (have i₁ := eq35868 (M.op X2 X0) X0
       have i₂ := eq38464 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq38464 eq35868
    | exact resolve eq35868 eq38464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39544 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38840 X0 X1 X2 X3
       have i₂ := eq256 (M.op X0 X1)
       grind)
    | exact superpose eq256 eq38840
    | exact resolve eq38840 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38840
  have eq39559 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38823 X0 X1 X2
       have i₂ := eq256 (M.op X0 X1)
       grind)
    | exact superpose eq256 eq38823
    | exact resolve eq38823 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq38823
  have eq39742 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39544 X0 X1 X2 X3
       have i₂ := eq24534 X1 X0
       grind)
    | exact superpose eq24534 eq39544
    | exact resolve eq39544 eq24534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39544
  have eq39746 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39559 X0 X1 X2
       have i₂ := eq24534 X1 X0
       grind)
    | exact superpose eq24534 eq39559
    | exact resolve eq39559 eq24534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39559
  have eq45054 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5884 eq56
    | exact resolve eq56 eq5884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45080 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5884 eq58
    | exact resolve eq58 eq5884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5884
  have eq45125 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45080
       have i₂ := eq24534 sF2 sF3
       grind)
    | exact superpose eq24534 eq45080
    | exact resolve eq45080 eq24534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45080
  have eq53673 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9367 X0 X1 X2 X3
       have i₂ := eq24534 X1 X0
       grind)
    | exact superpose eq24534 eq9367
    | exact resolve eq9367 eq24534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9367 eq24534
  have eq54164 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53673 X0 X1 X0 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq53673
    | exact resolve eq53673 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53673
  have eq55660 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54164 X1 X2
       have i₂ := eq38464 X1 X2 X0
       grind)
    | (have i₁ := eq54164 X0 (M.op X2 X0)
       have i₂ := eq38464 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq38464 eq54164
    | exact resolve eq54164 eq38464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38464 eq54164
  have eq111185 : y = (M.op x (M.op y x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq35864 eq33686
    | exact resolve eq33686 eq35864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33686 eq35864
  have eq127684 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq45125 eq35868
    | exact resolve eq35868 eq45125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127796 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq127684
    | exact resolve eq127684 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127684
  have eq127820 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq127796 eq105
    | exact resolve eq105 eq127796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq127796
  have eq133819 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq35868 x y
       have i₂ := eq111185
       grind)
    | exact superpose eq111185 eq35868
    | exact resolve eq35868 eq111185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35868
  have eq133932 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq133819
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq133819
    | exact resolve eq133819 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133819
  have eq133971 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq133932 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq133932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133932
  have eq133972 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq133971
    | exact resolve eq133971 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133971
  have eq133988 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq133972
       have r₂ := eq28
       grind)
    | exact resolve eq133972 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133972
  have eq134864 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq133988 eq56
    | exact resolve eq56 eq133988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134926 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ y) (σ x))) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq133988 eq25057
    | exact resolve eq25057 eq133988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133988
  have eq134969 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq134926 x
       have i₂ := eq39742 sF3 sF2 x sF3
       grind)
    | exact superpose eq39742 eq134926
    | exact resolve eq134926 eq39742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134926
  have eq137350 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq134864 eq17242
    | exact resolve eq17242 eq134864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134864
  have eq146955 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq137350 eq134969
    | exact resolve eq134969 eq137350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134969 eq137350
  have eq147042 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq146955
  have eq147063 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq147042
       have i₂ := eq56 sF2
       grind)
    | exact superpose eq56 eq147042
    | exact resolve eq147042 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147042
  have eq147064 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq147063
  have eq147848 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op (M.op x y) (M.op x X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq55660 y x X0
       have i₂ := eq147064
       grind)
    | exact superpose eq147064 eq55660
    | exact resolve eq55660 eq147064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55660 eq147064
  have eq160086 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op y x) = (M.op y y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5659 y
       have i₂ := eq127820
       grind)
    | exact superpose eq127820 eq5659
    | (have j0 := eq5659 y
       grind)
    | exact resolve eq5659 eq127820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5659 eq127820
  have eq160409 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq160086
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq160086
    | exact resolve eq160086 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160086
  have eq160436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq160409
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq160409
    | exact resolve eq160409 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160409
  have eq160449 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq160436
    | exact resolve eq160436 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160436
  have eq160456 : (M.op y x) = (M.op y y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq160449
       have r₂ := eq28
       grind)
    | exact resolve eq160449 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160449
  have eq164207 : y = (M.op x (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq147848 (M.op y x)
       have i₂ := eq111185
       grind)
    | exact superpose eq111185 eq147848
    | exact resolve eq147848 eq111185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147848
  have eq164349 : y = (M.op x (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq164207
  have eq164393 : y = (M.op x (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq4278 eq164349
    | exact resolve eq164349 eq4278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278 eq164349
  have eq170581 : y = (M.op y (M.op y x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq160456
       grind)
    | exact superpose eq160456 eq56
    | exact resolve eq56 eq160456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170646 : ∀ X0 : G, y = (M.op (M.op X0 (M.op y x)) (M.op y x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq25057 y y x
       have i₂ := eq160456
       grind)
    | exact superpose eq160456 eq25057
    | exact resolve eq25057 eq160456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25057 eq160456
  have eq170693 : y = (M.op x (M.op y x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq170646 x
       have i₂ := eq39742 y x x y
       grind)
    | exact superpose eq39742 eq170646
    | exact resolve eq170646 eq39742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39742 eq170646
  have eq172060 : (M.op x x) = (M.op y x) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17242 y x y
       have i₂ := eq170581
       grind)
    | exact superpose eq170581 eq17242
    | exact resolve eq17242 eq170581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17242 eq170581
  have eq173045 : y = (M.op x (M.op x x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq170693
       have i₂ := eq172060
       grind)
    | exact superpose eq172060 eq170693
    | exact resolve eq170693 eq172060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170693 eq172060
  have eq173146 : y = (M.op x (M.op x x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq173045
  have eq173169 : x = y ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq173146
       have i₂ := eq56 x
       grind)
    | exact superpose eq56 eq173146
    | exact resolve eq173146 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173146
  have eq173170 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq173169
  have eq173190 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq173170 eq45054
    | exact resolve eq45054 eq173170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45054
  have eq173227 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq173170 eq58
    | exact resolve eq58 eq173170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq173170
  have eq173286 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq173190
  have eq173405 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq173227 eq39221
    | exact resolve eq39221 eq173227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39221 eq173227
  have eq173446 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq173405 X0
       have i₂ := eq39746 (M.op X0 sF4) sF2 sF2
       grind)
    | exact superpose eq39746 eq173405
    | exact resolve eq173405 eq39746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39746 eq173405
  have eq215358 : (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq24316 x (M.op y y)
       have i₂ := eq164393
       grind)
    | exact superpose eq164393 eq24316
    | exact resolve eq24316 eq164393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24316 eq164393
  have eq236609 : y = (M.op x (M.op x x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq111185
       have i₂ := eq215358
       grind)
    | exact superpose eq215358 eq111185
    | exact resolve eq111185 eq215358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111185 eq215358
  have eq236728 : y = (M.op x (M.op x x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq236609
  have eq236748 : x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq236728
       have i₂ := eq56 x
       grind)
    | exact superpose eq56 eq236728
    | exact resolve eq236728 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq236728
  have eq236749 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq236748
  have eq236779 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq236749 eq173286
    | exact resolve eq173286 eq236749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173286
  have eq236791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq236779
  have eq236805 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq236791
       have r₂ := eq28
       grind)
    | exact resolve eq236791 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236791
  have eq236952 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq236805 eq173446
    | exact resolve eq173446 eq236805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173446 eq236805
  have eq237021 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq236952
  have eq239658 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq237021 eq45125
    | exact resolve eq45125 eq237021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45125 eq237021
  have eq239786 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq239658
  have eq239886 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq239786 eq236749
    | exact resolve eq236749 eq239786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236749 eq239786
  have eq239898 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq239886
  have eq239912 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq239898
       have r₂ := eq28
       grind)
    | exact resolve eq239898 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239898
  have eq239919 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq239912 eq30
    | exact resolve eq30 eq239912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq239912
  have eq240218 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq239919
    | exact resolve eq239919 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq239919
  have eq240219 : x = y := by grind
  clear eq240218
  have eq240247 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq240219
       grind)
    | exact superpose eq240219 eq19
    | exact resolve eq19 eq240219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq240248 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq240219
       grind)
    | exact superpose eq240219 eq25
    | exact resolve eq25 eq240219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq240219
  have eq240685 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq240248
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq240248
    | exact resolve eq240248 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq240248
  have eq240727 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq240685 eq27
    | exact resolve eq27 eq240685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq240685
  have eq241431 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq240727 eq75
    | exact resolve eq75 eq240727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq240727
  have eq241674 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq241431
       have i₂ := eq240247
       grind)
    | exact superpose eq240247 eq241431
    | exact resolve eq241431 eq240247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240247 eq241431
  have eq241759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq241674 eq15
    | exact resolve eq15 eq241674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241674
  have eq242180 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq241759
    | exact resolve eq241759 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq241759
  have eq242319 : False := by grind
  exact eq242319

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq70
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70
    | exact resolve eq70 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq73
    | exact resolve eq73 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq74
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq74
    | exact resolve eq74 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq79 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) := by
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
  have eq89 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15372 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq75 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq15372
    | exact resolve eq15372 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15372
  have eq15384 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq15373
       have r₂ := eq28
       grind)
    | exact resolve eq15373 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15373
  have eq15388 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq15384
    | exact resolve eq15384 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15384
  have eq15392 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq15388 eq89
    | (have r₁ := eq89
       have r₂ := eq15388
       grind)
    | exact resolve eq89 eq15388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq15388
  have eq15440 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq15392
  have eq15441 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq15440
  have eq15668 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq15441 eq75
    | exact resolve eq75 eq15441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq15441
  have eq15682 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq15668
  have eq15685 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq15682
       have r₂ := eq28
       grind)
    | exact resolve eq15682 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15682
  have eq15819 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq15685
       grind)
    | exact superpose eq15685 eq52
    | exact resolve eq52 eq15685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq15822 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq15685
       grind)
    | exact superpose eq15685 eq88
    | (have r₁ := eq88
       have r₂ := eq15685
       grind)
    | exact resolve eq88 eq15685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq15685
  have eq15868 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq15822
  have eq15869 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq15868
  have eq15890 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq15819
    | exact resolve eq15819 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15819
  have eq16156 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49
       have i₂ := eq15869
       grind)
    | exact superpose eq15869 eq49
    | exact resolve eq49 eq15869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq15869
  have eq16182 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq16156
    | exact resolve eq16156 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16156
  have eq16951 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16182 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq16182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16182
  have eq16952 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16951
  have eq16956 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq16952
    | exact resolve eq16952 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16952
  have eq16967 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16956
       have r₂ := eq28
       grind)
    | exact resolve eq16956 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16956
  have eq16971 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq16967
    | exact resolve eq16967 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16967
  have eq17370 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16971 eq15890
    | exact resolve eq15890 eq16971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15890 eq16971
  have eq17409 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17370
  have eq17422 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17409
       have r₂ := eq28
       grind)
    | exact resolve eq17409 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17409
  have eq17426 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq17422 eq30
    | exact resolve eq30 eq17422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17422
  have eq17548 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq17426
    | exact resolve eq17426 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17426
  have eq17549 : x = y := by grind
  clear eq17548
  have eq17568 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq17549
       grind)
    | exact superpose eq17549 eq19
    | exact resolve eq19 eq17549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq17569 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq17549
       grind)
    | exact superpose eq17549 eq25
    | exact resolve eq25 eq17549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17549
  have eq17679 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17569
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17569
    | exact resolve eq17569 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17569
  have eq17695 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17679 eq27
    | exact resolve eq27 eq17679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17679
  have eq17951 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq17695 eq79
    | exact resolve eq79 eq17695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq17695
  have eq18018 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq17951
       have i₂ := eq17568
       grind)
    | exact superpose eq17568 eq17951
    | exact resolve eq17951 eq17568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17568 eq17951
  have eq18029 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18018 eq15
    | exact resolve eq15 eq18018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18018
  have eq18078 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18029
    | exact resolve eq18029 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq18029
  have eq18087 : False := by grind
  exact eq18087

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_x_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq48 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
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
  have eq99 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq105 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
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
  clear eq48
  have eq180 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq99 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq99
    | exact resolve eq99 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq204 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq208 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq205 X0
       grind)
    | exact superpose eq205 eq11
    | (have j0 := eq11 (k X0 (M.op X0 X0)) X0
       grind)
    | exact resolve eq11 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X0)
       have i₂ := eq205 X0
       grind)
    | exact superpose eq205 eq16
    | exact resolve eq16 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq220 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq223 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq222 X0
       have j1 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq222 x
       have r₂ := eq13 (k x (M.op x x)) x
       grind)
    | (have r₁ := eq222 X0
       have r₂ := eq13 X0 (k X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq222 x
       have r₂ := eq13 (M.op x x) x
       grind)
    | exact resolve eq222 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq225 : (σ x) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq36 (M.op x x)
       have i₂ := eq223 x
       grind)
    | exact superpose eq223 eq36
    | exact resolve eq36 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq227 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq38 (M.op sF0 sF0)
       have i₂ := eq223 sF0
       grind)
    | exact superpose eq223 eq38
    | exact resolve eq38 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq228 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq105 (M.op sF2 sF2)
       have i₂ := eq223 sF2
       grind)
    | exact superpose eq223 eq105
    | exact resolve eq105 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq229 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq29 eq228
    | exact resolve eq228 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq230 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq227
    | exact resolve eq227 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq232 : (σ x) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq225
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq225
    | exact resolve eq225 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq268 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq223 (M.op X0 X0)
       have i₂ := eq221 X0 X0
       grind)
    | exact superpose eq221 eq223
    | exact resolve eq223 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq269 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq205 (M.op X0 X0)
       have i₂ := eq221 X0 X0
       grind)
    | exact superpose eq221 eq205
    | exact resolve eq205 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : (σ (M.op x x)) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq40 (M.op x x)
       have i₂ := eq268 x
       grind)
    | exact superpose eq268 eq40
    | exact resolve eq40 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq386 : (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (k (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op x y)) := by
    first
    | (have i₁ := eq180 (M.op sF1 sF1)
       have i₂ := eq268 sF1
       grind)
    | exact superpose eq268 eq180
    | exact resolve eq180 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq268
  have eq771 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) := by
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
  have eq773 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq207
       grind)
    | exact superpose eq207 eq41
    | exact resolve eq41 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq779 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq778
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq778
    | exact resolve eq778 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq781 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq20 eq779
    | exact resolve eq779 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq913 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq781 eq208
    | exact resolve eq208 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq913
       have r₂ := eq27
       grind)
    | exact resolve eq913 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq1067 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq920 eq773
    | (have r₁ := eq773
       have r₂ := eq920
       grind)
    | exact resolve eq773 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq1068 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq1067
  have eq1069 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq1068
  have eq1070 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq781 eq1069
    | exact resolve eq1069 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq1069
  have eq1071 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1070
       have r₂ := eq27
       grind)
    | exact resolve eq1070 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1072 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq771
       have i₂ := eq1071
       grind)
    | exact superpose eq1071 eq771
    | (have r₁ := eq771
       have r₂ := eq1071
       grind)
    | exact resolve eq771 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771 eq1071
  have eq1086 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq1072
  have eq1087 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1086
  have eq1134 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1087
       grind)
    | exact superpose eq1087 eq41
    | exact resolve eq41 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1087
  have eq1135 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1134
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1134
    | exact resolve eq1134 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq1137 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq1135
    | exact resolve eq1135 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1154 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1137 eq208
    | exact resolve eq208 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq1158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1154
  have eq1163 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1158
       have r₂ := eq27
       grind)
    | exact resolve eq1158 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1167 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1163 eq773
    | (have r₁ := eq773
       have r₂ := eq1163
       grind)
    | exact resolve eq773 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773 eq1163
  have eq1185 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq1167
  have eq1186 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq1185
  have eq1187 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1137 eq1186
    | exact resolve eq1186 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137 eq1186
  have eq1188 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1187
       have r₂ := eq27
       grind)
    | exact resolve eq1187 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1190 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1188 eq31
    | exact resolve eq31 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1188
  have eq1218 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1190
    | exact resolve eq1190 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq1219 : x = y := by grind
  clear eq1218
  have eq1222 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1219
       grind)
    | exact superpose eq1219 eq18
    | exact resolve eq18 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1223 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1219
       grind)
    | exact superpose eq1219 eq24
    | exact resolve eq24 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1219
  have eq1236 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1223
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1223
    | exact resolve eq1223 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1237 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1236 eq26
    | exact resolve eq26 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1236
  have eq1274 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq383
       have i₂ := eq1222
       grind)
    | exact superpose eq1222 eq383
    | exact resolve eq383 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq1276 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq232
       have i₂ := eq1222
       grind)
    | exact superpose eq1222 eq232
    | exact resolve eq232 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq1284 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq269 x
       have i₂ := eq1222
       grind)
    | exact superpose eq1222 eq269
    | exact resolve eq269 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1285 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq221 x x
       have i₂ := eq1222
       grind)
    | exact superpose eq1222 eq221
    | exact resolve eq221 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1288 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1276
    | exact resolve eq1276 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1289 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq1274
    | exact resolve eq1274 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq1297 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) X1)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1237 eq16
    | exact resolve eq16 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1299 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1237 eq221
    | exact resolve eq221 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1303 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1237 eq269
    | exact resolve eq269 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq1304 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1237 eq221
    | exact resolve eq221 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1334 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op (M.op x y) X1)) x) := by
    intro X0 X1
    first
    | exact superpose eq1285 eq16
    | exact resolve eq16 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1392 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1304 eq16
    | exact resolve eq16 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1409 : x ≠ (M.op x x) ∨ (M.op x x) = (M.op x (τ (M.op (σ x) (σ x)))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq229 eq214
    | (have j0 := eq214 x (τ (M.op (σ x) (σ x)))
       grind)
    | exact resolve eq214 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq1416 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq230 eq214
    | (have j0 := eq214 (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))
       grind)
    | exact resolve eq214 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq230
  have eq1426 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq1285 eq1416
    | exact resolve eq1416 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416
  have eq1432 : x ≠ (M.op x y) ∨ (M.op x x) = (M.op x (τ (M.op (σ x) (σ x)))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1409
       have i₂ := eq1222
       grind)
    | exact superpose eq1222 eq1409
    | exact resolve eq1409 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq1437 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1426
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1426
    | exact resolve eq1426 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq1443 : (M.op x x) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x ≠ (M.op x y) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1237 eq1432
    | exact resolve eq1432 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq1447 : (σ x) = (σ (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1285 eq1437
    | exact resolve eq1437 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285 eq1437
  have eq1450 : (M.op x y) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x ≠ (M.op x y) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1443
       have i₂ := eq1222
       grind)
    | exact superpose eq1222 eq1443
    | exact resolve eq1443 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222 eq1443
  have eq1454 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1447
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1447
    | exact resolve eq1447 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1447
  have eq1457 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1237 eq1450
    | exact resolve eq1450 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450
  have eq1500 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op x X1)) (M.op X0 (M.op x X1)))) := by
    intro X0 X1
    first
    | exact superpose eq1284 eq204
    | exact resolve eq204 eq1284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1550 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq1304 eq204
    | exact resolve eq204 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq1744 : ∀ X0 : G, (σ x) = (M.op (k X0 (σ x)) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq1299 X0
       have i₂ := eq11 X0 sF2
       grind)
    | exact superpose eq11 eq1299
    | (have j1 := eq11 X0 (σ x)
       grind)
    | exact resolve eq1299 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq1830 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k X0 (σ x)) (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq1392 X0
       have i₂ := eq11 X0 sF2
       grind)
    | exact superpose eq11 eq1392
    | (have j1 := eq11 X0 (σ x)
       grind)
    | exact resolve eq1392 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq3740 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq1304 eq1550
    | exact resolve eq1550 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550
  have eq3798 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X1 (M.op X0 (σ x))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq3740 eq1297
    | exact resolve eq1297 eq3740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq4681 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1289 eq1744
    | (have j0 := eq1744 (σ (M.op x y))
       grind)
    | exact resolve eq1744 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744
  have eq4719 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x))) ∨ (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4681 eq205
    | exact resolve eq205 eq4681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4681
  have eq4738 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4719 eq3798
    | exact resolve eq3798 eq4719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3798 eq4719
  have eq4753 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4738
  have eq4774 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ x)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq4753 eq16
    | exact resolve eq16 eq4753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4753
  have eq4803 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1303 eq4774
    | exact resolve eq4774 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4774
  have eq5030 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1289 eq1830
    | (have j0 := eq1830 (σ (M.op x y))
       grind)
    | exact resolve eq1830 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1830
  have eq5073 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5030 eq205
    | exact resolve eq205 eq5030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq5030
  have eq5094 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5073
       have i₂ := eq11 sF1 sF2
       grind)
    | exact superpose eq11 eq5073
    | (have j1 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq5073 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5073
  have eq5112 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq5094
  have eq5116 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1289 eq5112
    | exact resolve eq5112 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5112
  have eq5118 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq5116
       have r₂ := eq1454
       grind)
    | exact resolve eq5116 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454 eq5116
  have eq5119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1289 eq5118
    | exact resolve eq5118 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289 eq5118
  have eq5120 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq5119
       have r₂ := eq27
       grind)
    | exact resolve eq5119 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5119
  have eq5125 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5120 eq4803
    | exact resolve eq4803 eq5120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4803
  have eq5144 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5120 eq221
    | exact resolve eq221 eq5120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5120
  have eq5148 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq5125
  have eq5388 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5144 eq3740
    | exact resolve eq3740 eq5144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3740 eq5144
  have eq5429 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5388 eq5148
    | exact resolve eq5148 eq5388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5148 eq5388
  have eq5452 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq5429
  have eq5512 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5452
       have i₂ := eq11 sF2 sF1
       grind)
    | exact superpose eq11 eq5452
    | (have j1 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq5452 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5531 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq5512
  have eq5544 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1288 eq5531
    | exact resolve eq5531 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288 eq5531
  have eq5548 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1303 eq5544
    | exact resolve eq5544 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303 eq5544
  have eq5550 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq5548
       have r₂ := eq27
       grind)
    | exact resolve eq5548 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5548
  have eq5551 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1237 eq5550
    | exact resolve eq5550 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5550
  have eq5553 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5551 eq5452
    | exact resolve eq5452 eq5551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5452 eq5551
  have eq5576 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq5553
  have eq5580 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1304 eq5576
    | exact resolve eq5576 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304 eq5576
  have eq5581 : (σ (M.op x y)) = (σ x) := by grind
  clear eq5580
  have eq5584 : (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq5581 eq28
    | exact resolve eq28 eq5581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq5598 : (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) (M.op x y)) := by
    first
    | exact superpose eq5581 eq386
    | exact resolve eq386 eq5581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq5581
  have eq5605 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq1237 eq5598
    | exact resolve eq5598 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237 eq5598
  have eq5629 : x = (M.op x y) := by
    first
    | exact superpose eq5584 eq29
    | exact resolve eq29 eq5584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5584
  have eq5689 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op (M.op x y) X1)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1334 X0 X1
       have i₂ := eq5629
       grind)
    | exact superpose eq5629 eq1334
    | exact resolve eq1334 eq5629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5693 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1457
       have i₂ := eq5629
       grind)
    | exact superpose eq5629 eq1457
    | (have r₁ := eq1457
       have r₂ := eq5629
       grind)
    | exact resolve eq1457 eq5629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457
  have eq5704 : (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq5693
  have eq7146 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5704 eq221
    | exact resolve eq221 eq5704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5704
  have eq9473 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (τ (M.op (σ x) (σ y)))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq7146 eq5689
    | exact resolve eq5689 eq7146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5689
  have eq19108 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X2 (M.op X0 (M.op x X1))) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq1500 eq1334
    | exact resolve eq1334 eq1500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334 eq1500
  have eq19131 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X2 (M.op X0 (M.op (M.op x y) X1))) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19108 X0 X1 X2
       have i₂ := eq5629
       grind)
    | exact superpose eq5629 eq19108
    | exact resolve eq19108 eq5629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5629 eq19108
  have eq19212 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq19131 (M.op sF0 x) x (M.op x (M.op (M.op sF0 x) x))
       have i₂ := eq16 (M.op sF0 x) x x
       grind)
    | exact superpose eq16 eq19131
    | exact resolve eq19131 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19131
  have eq19280 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq7146 eq19212
    | exact resolve eq19212 eq7146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7146 eq19212
  have eq19456 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq19280 eq11
    | (have j0 := eq11 (M.op x y) (k (τ (M.op (σ x) (σ y))) (M.op x y))
       grind)
    | exact resolve eq11 eq19280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19280
  have eq19464 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq19456
  have eq19467 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5605 eq19464
    | exact resolve eq19464 eq5605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5605 eq19464
  have eq19468 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq19467
  have eq19583 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op X0 (τ (M.op (σ x) (σ y)))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq19468 eq221
    | exact resolve eq221 eq19468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq19468
  have eq19600 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f19600_13 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op X0 (τ (M.op (σ x) (σ y)))) (M.op x y)) ∨ (τ (M.op (σ x) (σ y))) = (M.op x y) := by
      intro X0
      grind
    have f19600_14 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (τ (M.op (σ x) (σ y)))) (M.op x y)) ∨ (τ (M.op (σ x) (σ y))) = (M.op x y) := by
      intro X0
      grind
    have f19600_24 : (τ (M.op (σ x) (σ y))) ≠ (M.op x y) := by grind
    have f19600_26 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (τ (M.op (σ x) (σ y)))) (M.op x y)) := by
      intro X0
      first
      | (have j0 := f19600_14 X0
         grind)
      | (have r₁ := f19600_14 X0
         have r₂ := f19600_24
         grind)
      | exact resolve f19600_14 f19600_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f19600_27 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op X0 (τ (M.op (σ x) (σ y)))) (M.op x y)) := by
      intro X0
      first
      | (have j0 := f19600_13 X0
         grind)
      | (have r₁ := f19600_13 X0
         have r₂ := f19600_24
         grind)
      | exact resolve f19600_13 f19600_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f19600_28 : (τ (M.op (σ x) (σ y))) = (M.op x y) := by
      first
      | (have i₁ := f19600_27 x
         have i₂ := f19600_26 x
         grind)
      | exact superpose f19600_26 f19600_27
      | exact resolve f19600_27 f19600_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f19600_29 : False := by
      first
      | (have r₁ := f19600_28
         have r₂ := f19600_24
         grind)
      | exact resolve f19600_28 f19600_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f19600_29
  clear eq9473 eq19583
  have eq19601 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq19600
  have eq19622 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19601 eq14
    | exact resolve eq14 eq19601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19601
  have eq19693 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq19622
    | exact resolve eq19622 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq19622
  have eq19719 : False := by grind
  exact eq19719

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_y_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
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
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq78
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq78
    | exact resolve eq78 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq84
    | exact resolve eq84 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq86
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86
    | exact resolve eq86 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
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
  have eq113 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq116 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by grind
  clear eq113
  have eq117 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq116
  have eq164 : (σ (k x (M.op (M.op x y) (M.op x y)))) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq117 eq36
    | exact resolve eq36 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq183 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq249 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq58
    | (have j0 := eq58 (σ y) (σ x)
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 X0)
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq275 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq11 (τ X0) X1
       grind)
    | exact superpose eq11 eq35
    | (have j1 := eq11 (τ X0) X1
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq285 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq274 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq274
    | exact resolve eq274 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq286 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq285
  have eq385 : (σ (M.op (k x y) (k x y))) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq45 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq45
    | exact resolve eq45 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 y x X0 X1
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq55
    | (have j0 := eq55 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq55 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X1 X0) X1 X2 (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq519 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op X2 (M.op X1 (M.op (σ x) (σ y)))) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq629 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq75
  have eq667 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq286 X0
       grind)
    | exact superpose eq286 eq16
    | exact resolve eq16 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq752 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq629 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq629
    | (have j0 := eq629 x X0
       grind)
    | exact resolve eq629 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq931 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq253 (τ X0)
       have i₂ := eq667 X0
       grind)
    | exact superpose eq667 eq253
    | exact resolve eq253 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq667
  have eq2536 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (σ X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq402 (M.op X0 X0) X1
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq402
    | exact resolve eq402 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4652 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq517 x X1 X0
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq517
    | exact resolve eq517 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq4671 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq4652 sF0 sF0
       have i₂ := eq56 sF0
       grind)
    | exact superpose eq56 eq4652
    | exact resolve eq4652 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4652
  have eq4723 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq519 sF2 X1 x
       have i₂ := eq58 sF2 sF2
       grind)
    | exact superpose eq58 eq519
    | exact resolve eq519 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq4848 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq4723 sF4 sF4
       have i₂ := eq56 sF4
       grind)
    | exact superpose eq56 eq4723
    | exact resolve eq4723 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4723
  have eq4907 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq508 (M.op y X0) X0
       have i₂ := eq58 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq58 eq508
    | exact resolve eq508 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq4959 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq510 (M.op sF3 x) x
       have i₂ := eq58 (M.op sF3 x) (M.op sF3 x)
       grind)
    | exact superpose eq58 eq510
    | exact resolve eq510 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq5069 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq515 X0 X2 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq56 (M.op X0 X1)
       grind)
    | exact superpose eq56 eq515
    | exact resolve eq515 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5136 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq515 X0 X0 X2 X3 X1
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq515
    | exact resolve eq515 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq5792 : ∀ X0 : G, (σ (k X0 y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq183 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq6267 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq275 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq275
    | exact resolve eq275 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq6331 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6267 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq6267
    | (have j0 := eq6267 X0 X1
       grind)
    | exact resolve eq6267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6267
  have eq6374 : (σ (k x (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq117 eq752
    | exact resolve eq752 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq6493 : (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq164 eq6374
    | exact resolve eq6374 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq6374
  have eq6509 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq6493
       have i₂ := eq58 sF0 sF0
       grind)
    | exact superpose eq58 eq6493
    | exact resolve eq6493 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6493
  have eq6520 : (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq6509
    | exact resolve eq6509 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6509
  have eq10236 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq514 (M.op X1 X2) X1 X2 (M.op X1 X2) x x
       have i₂ := eq56 (M.op X1 X2)
       grind)
    | exact superpose eq56 eq514
    | exact resolve eq514 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq514
  have eq16660 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16661 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16660
    | exact resolve eq16660 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16660
  have eq16672 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq16661
       have r₂ := eq28
       grind)
    | exact resolve eq16661 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16661
  have eq16676 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16672
    | exact resolve eq16672 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16672
  have eq16679 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq16676 eq249
    | exact resolve eq249 eq16676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq16708 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq16676 eq931
    | exact resolve eq931 eq16676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq16739 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq16708
    | exact resolve eq16708 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16708
  have eq16749 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq16679 eq54
    | exact resolve eq54 eq16679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq17897 : y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq16739 eq58
    | exact resolve eq58 eq16739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16739
  have eq38084 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16676 eq5069
    | (have j0 := eq5069 (σ y) X0 (σ x)
       grind)
    | exact resolve eq5069 eq16676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38327 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16679 eq38084
    | exact resolve eq38084 eq16679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16679 eq38084
  have eq38380 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38327 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38327
  have eq38432 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) X0) ∨ (σ y) = (k (M.op (σ y) X0) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq38380 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq38380 X0
       grind)
    | exact resolve eq12 eq38380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38380
  have eq38473 : ∀ X0 : G, (σ y) = (k (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38432 X0
       grind)
    | (have r₁ := eq38432 X0
       have r₂ := eq16676
       grind)
    | exact resolve eq38432 eq16676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16676 eq38432
  have eq51079 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op (M.op y X0) (M.op y X0))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq17897 eq10236
    | exact resolve eq10236 eq17897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10236 eq17897
  have eq51601 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op (M.op x y) (M.op y X0))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq51079 X0
       have i₂ := eq4907 X0
       grind)
    | exact superpose eq4907 eq51079
    | exact resolve eq51079 eq4907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51079
  have eq77808 : ∀ X0 : G, (M.op y y) = (M.op (M.op y X0) y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq51601 eq5136
    | exact resolve eq5136 eq51601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5136 eq51601
  have eq202713 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq16749 eq38473
    | exact resolve eq38473 eq16749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16749 eq38473
  have eq202799 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq202713
  have eq202814 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq202799 eq62
    | exact resolve eq62 eq202799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202815 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq202799 eq87
    | exact resolve eq87 eq202799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq202799
  have eq202837 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq202815
  have eq202849 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq30 eq202814
    | exact resolve eq202814 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202814
  have eq202859 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq202837
       grind)
    | exact superpose eq202837 eq99
    | exact resolve eq99 eq202837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202890 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq402 y x
       have i₂ := eq202837
       grind)
    | exact superpose eq202837 eq402
    | exact resolve eq402 eq202837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202837
  have eq202970 : (σ y) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq202890 x
       have i₂ := eq2536 sF0 x
       grind)
    | exact superpose eq2536 eq202890
    | exact resolve eq202890 eq2536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202890
  have eq202988 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq202859
    | exact resolve eq202859 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202859
  have eq203002 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq117 eq202970
    | exact resolve eq202970 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202970
  have eq203012 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq203002
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq203002
    | exact resolve eq203002 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203002
  have eq208082 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq402 y x
       have i₂ := eq202849
       grind)
    | exact superpose eq202849 eq402
    | exact resolve eq402 eq202849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq202849
  have eq208163 : (σ y) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq208082 x
       have i₂ := eq2536 sF0 x
       grind)
    | exact superpose eq2536 eq208082
    | exact resolve eq208082 eq2536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2536 eq208082
  have eq208194 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq117 eq208163
    | exact resolve eq208163 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq208163
  have eq208204 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq208194
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq208194
    | exact resolve eq208194 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208194
  have eq227530 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq208204 eq6520
    | exact resolve eq6520 eq208204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208204
  have eq227531 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq203012 eq6520
    | exact resolve eq6520 eq203012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6520 eq203012
  have eq227539 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq227531
  have eq227540 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by grind
  clear eq227530
  have eq227546 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq227539
    | exact resolve eq227539 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227539
  have eq227547 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq27 eq227540
    | exact resolve eq227540 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227540
  have eq227549 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq227546
    | exact resolve eq227546 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227546
  have eq227550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq27 eq227547
    | exact resolve eq227547 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227547
  have eq227552 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq227549
       have r₂ := eq28
       grind)
    | exact resolve eq227549 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227549
  have eq227553 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have r₁ := eq227550
       have r₂ := eq28
       grind)
    | exact resolve eq227550 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227550
  have eq227848 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq227553 eq62
    | exact resolve eq62 eq227553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq227553
  have eq228256 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq6331 x y
       have i₂ := eq227848
       grind)
    | exact superpose eq227848 eq6331
    | (have j0 := eq6331 x y
       grind)
    | exact resolve eq6331 eq227848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6331 eq227848
  have eq228258 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq228256
  have eq228266 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq228258
       have r₂ := eq12 x y
       grind)
    | exact resolve eq228258 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228258
  have eq228296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq228266
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq228266
    | exact resolve eq228266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228266
  have eq228317 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq228296
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq228296
    | exact resolve eq228296 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228296
  have eq228329 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | exact superpose eq21 eq228317
    | exact resolve eq228317 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228317
  have eq228337 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq228329
       have r₂ := eq28
       grind)
    | exact resolve eq228329 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228329
  have eq228362 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq228337
       grind)
    | exact superpose eq228337 eq49
    | exact resolve eq49 eq228337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq228369 : (σ (M.op y y)) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq385
       have i₂ := eq228337
       grind)
    | exact superpose eq228337 eq385
    | exact resolve eq385 eq228337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq228381 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5792 x
       have i₂ := eq228337
       grind)
    | exact superpose eq228337 eq5792
    | (have j0 := eq5792 x
       grind)
    | exact resolve eq5792 eq228337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5792 eq228337
  have eq228406 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq228381
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq228381
    | exact resolve eq228381 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228381
  have eq228416 : (M.op (σ y) (σ y)) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq228369
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq228369
    | exact resolve eq228369 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228369
  have eq228423 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq228362
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq228362
    | exact resolve eq228362 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228362
  have eq228432 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq228406
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq228406
    | exact resolve eq228406 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228406
  have eq228444 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq228432
    | exact resolve eq228432 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228432
  have eq228453 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq228444
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq228444
    | exact resolve eq228444 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228444
  have eq228454 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq228453
  have eq228507 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq228423 eq227552
    | exact resolve eq227552 eq228423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227552
  have eq228523 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq228507
  have eq228664 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq228523 eq4848
    | exact resolve eq4848 eq228523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4848
  have eq266774 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq228664 eq4959
    | exact resolve eq4959 eq228664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4959 eq228664
  have eq266862 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq266774
       have i₂ := eq58 sF2 sF2
       grind)
    | exact superpose eq58 eq266774
    | exact resolve eq266774 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266774
  have eq307969 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq228523 eq266862
    | exact resolve eq266862 eq228523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228523 eq266862
  have eq308061 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq307969
  have eq367247 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (k (σ x) (σ y)) X0) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq228416 eq5069
    | exact resolve eq5069 eq228416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5069 eq228416
  have eq367273 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (k (σ x) (σ y)) X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq367247 X0
       have i₂ := eq58 sF3 sF3
       grind)
    | exact superpose eq58 eq367247
    | exact resolve eq367247 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367247
  have eq378891 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq228423 eq367273
    | exact resolve eq367273 eq228423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228423 eq367273
  have eq379076 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq378891 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378891
  have eq379097 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq308061 eq379076
    | exact resolve eq379076 eq308061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308061 eq379076
  have eq379359 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq379097
  have eq379378 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq379359
    | exact resolve eq379359 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379359
  have eq379457 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq379378 eq202988
    | exact resolve eq202988 eq379378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202988 eq379378
  have eq379682 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq379457
  have eq379769 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq379682
       have r₂ := eq28
       grind)
    | exact resolve eq379682 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379682
  have eq379782 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq379769 eq30
    | exact resolve eq30 eq379769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379968 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq379782
    | exact resolve eq379782 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379782
  have eq379969 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq379968
  have eq379990 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq379969 eq30
    | exact resolve eq30 eq379969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379969
  have eq381072 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq379990
    | exact resolve eq379990 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq379990
  have eq381263 : (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq381072 eq4671
    | exact resolve eq4671 eq381072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4671
  have eq384845 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq4907 x
       have i₂ := eq381263
       grind)
    | exact superpose eq381263 eq4907
    | exact resolve eq4907 eq381263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4907 eq381263
  have eq384930 : x = (M.op (M.op x y) (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq384845
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq384845
    | exact resolve eq384845 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq384845
  have eq390787 : x = (M.op y (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq381072 eq384930
    | exact resolve eq384930 eq381072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381072 eq384930
  have eq390870 : x = (M.op y (M.op x x)) ∨ x = y := by grind
  clear eq390787
  have eq394151 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq77808 (M.op x x)
       have i₂ := eq390870
       grind)
    | exact superpose eq390870 eq77808
    | exact resolve eq77808 eq390870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77808 eq390870
  have eq394232 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq394151
  have eq394245 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq394232
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq394232
    | exact resolve eq394232 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394232
  have eq394246 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq394245
  have eq411347 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq99
       have i₂ := eq394246
       grind)
    | exact superpose eq394246 eq99
    | exact resolve eq99 eq394246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq394246
  have eq411544 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq411347
    | exact resolve eq411347 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411347
  have eq418338 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq411544 eq228454
    | exact resolve eq228454 eq411544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228454 eq411544
  have eq418579 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq418338
  have eq418684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq418579
       have r₂ := eq379769
       grind)
    | exact resolve eq418579 eq379769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379769 eq418579
  have eq418708 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq418684
       have r₂ := eq28
       grind)
    | exact resolve eq418684 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418684
  have eq418716 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq418708 eq30
    | exact resolve eq30 eq418708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq418708
  have eq418971 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq418716
    | exact resolve eq418716 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq418716
  have eq418972 : x = y := by grind
  clear eq418971
  have eq418991 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq418972
       grind)
    | exact superpose eq418972 eq19
    | exact resolve eq19 eq418972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq418992 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq418972
       grind)
    | exact superpose eq418972 eq25
    | exact resolve eq25 eq418972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq418972
  have eq419332 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq418992
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq418992
    | exact resolve eq418992 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq418992
  have eq420653 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq419332 eq27
    | exact resolve eq27 eq419332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq419332
  have eq421207 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq420653 eq72
    | exact resolve eq72 eq420653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq420653
  have eq421402 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq421207
       have i₂ := eq418991
       grind)
    | exact superpose eq418991 eq421207
    | exact resolve eq421207 eq418991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418991 eq421207
  have eq423718 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq421402 eq15
    | exact resolve eq15 eq421402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421402
  have eq424233 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq423718
    | exact resolve eq423718 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq423718
  have eq424375 : False := by grind
  exact eq424375

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq50 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq70
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70
    | exact resolve eq70 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq73
    | exact resolve eq73 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq74
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq74
    | exact resolve eq74 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq79 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq88 : y ≠ (M.op x y) ∨ x = y ∨ (k x y) = (M.op y y) := by
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
  have eq89 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq100 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq96
  have eq101 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq100
  have eq115 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq118 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq115
  have eq119 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq118
  have eq132 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq101
       grind)
    | exact superpose eq101 eq16
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq119 eq16
    | exact resolve eq16 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq255 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X2
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq836 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq982 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq75 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq983 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq982
    | exact resolve eq982 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq986 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq983
       have r₂ := eq28
       grind)
    | exact resolve eq983 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq988 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq986
    | exact resolve eq986 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq990 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq988 eq89
    | (have r₁ := eq89
       have r₂ := eq988
       grind)
    | exact resolve eq89 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq993 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq988 eq54
    | exact resolve eq54 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq995 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq990
  have eq996 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq995
  have eq1002 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq996 eq75
    | exact resolve eq75 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq996
  have eq1006 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1002
  have eq1099 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1006 eq58
    | exact resolve eq58 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq1236 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ (M.op x y)) X1)) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq1099 eq14
    | exact resolve eq14 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1246 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1099 eq14
    | exact resolve eq14 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq2175 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq1246
    | (have j0 := eq1246 (σ x)
       grind)
    | exact resolve eq1246 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq3333 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq993
    | (have j0 := eq993 (σ x)
       grind)
    | exact resolve eq993 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq3357 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq988 eq3333
    | exact resolve eq3333 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988 eq3333
  have eq3367 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3357
  have eq3382 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3367 eq14
    | exact resolve eq14 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3367
  have eq3654 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq709 X0 X2 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq56 (M.op X0 X1)
       grind)
    | exact superpose eq56 eq709
    | exact resolve eq709 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq4879 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq836 x y
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq836
    | (have j0 := eq836 x y
       grind)
    | exact resolve eq836 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq4902 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4879
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4879
    | exact resolve eq4879 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4879
  have eq4933 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4902
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4902
    | exact resolve eq4902 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4902
  have eq4964 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4933
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4933
    | exact resolve eq4933 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4933
  have eq4994 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq4964
    | exact resolve eq4964 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4964
  have eq5023 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq4994
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4994
    | exact resolve eq4994 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4994
  have eq5041 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5023
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5023
    | exact resolve eq5023 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5023
  have eq22843 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3382 eq255
    | exact resolve eq255 eq3382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq3382
  have eq23419 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2175 eq22843
    | exact resolve eq22843 eq2175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175 eq22843
  have eq23458 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq23419
  have eq23501 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq23458 eq56
    | exact resolve eq56 eq23458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq23458
  have eq23555 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq23501 eq1236
    | exact resolve eq1236 eq23501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236 eq23501
  have eq23575 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq23555
  have eq23576 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq23575
    | exact resolve eq23575 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23575
  have eq23577 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq23576
       have r₂ := eq28
       grind)
    | exact resolve eq23576 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23576
  have eq23579 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq23577 eq30
    | exact resolve eq30 eq23577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq23577
  have eq23622 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq23579
    | exact resolve eq23579 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23579
  have eq23623 : y = (M.op x y) ∨ x = y := by grind
  clear eq23622
  have eq23631 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq23623 eq21
    | exact resolve eq21 eq23623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23632 : (σ (k x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq23623 eq50
    | exact resolve eq50 eq23623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq23633 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op x x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq23623 eq53
    | exact resolve eq53 eq23623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq23635 : y ≠ y ∨ x = y ∨ (k x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq23623 eq88
    | (have r₁ := eq88
       have r₂ := eq23623
       grind)
    | exact resolve eq88 eq23623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq23697 : y ≠ y ∨ x = y ∨ (k x y) = (M.op y y) := by grind
  clear eq23635
  have eq23698 : (k x y) = (M.op y y) ∨ x = y := by grind
  clear eq23697
  have eq23748 : (k (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq23632
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq23632
    | exact resolve eq23632 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23632
  have eq23749 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq23631
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23631
    | exact resolve eq23631 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23631
  have eq23782 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq23749 eq132
    | exact resolve eq132 eq23749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq23838 : (σ (M.op x y)) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq23749 eq5041
    | exact resolve eq5041 eq23749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5041 eq23749
  have eq24167 : (σ (M.op x y)) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq23838
       have r₂ := eq28
       grind)
    | exact resolve eq23838 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23838
  have eq24191 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq165 eq23782
    | exact resolve eq23782 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq23782
  have eq24251 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq23698
       grind)
    | exact superpose eq23698 eq49
    | exact resolve eq49 eq23698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq23698
  have eq24287 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq24251
       have i₂ := eq101
       grind)
    | exact superpose eq101 eq24251
    | exact resolve eq24251 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24251
  have eq25303 : (k (σ x) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq24287 eq23748
    | exact resolve eq23748 eq24287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23748 eq24287
  have eq25309 : (k (σ x) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq25303
  have eq29090 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq25309 eq24167
    | exact resolve eq24167 eq25309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24167 eq25309
  have eq29093 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq29090
  have eq30522 : x = (M.op (M.op x y) (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq23633 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq23633
    | (have j0 := eq23633 x
       grind)
    | exact resolve eq23633 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23633
  have eq49990 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op x y) X0) (M.op (M.op y y) (M.op y y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq24191 eq3654
    | exact resolve eq3654 eq24191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3654 eq24191
  have eq50131 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op x y) X0) y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq49990 X0
       have i₂ := eq58 y y
       grind)
    | exact superpose eq58 eq49990
    | exact resolve eq49990 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq49990
  have eq50534 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq30522 eq50131
    | exact resolve eq50131 eq30522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30522 eq50131
  have eq50629 : (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq50534
  have eq50634 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq50629
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq50629
    | exact resolve eq50629 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50629
  have eq50637 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq101
       have i₂ := eq50634
       grind)
    | exact superpose eq50634 eq101
    | exact resolve eq101 eq50634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq50634
  have eq50781 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq50637
    | exact resolve eq50637 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50637
  have eq51308 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq50781 eq29093
    | (have r₁ := eq29093
       have r₂ := eq50781
       grind)
    | exact resolve eq29093 eq50781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29093 eq50781
  have eq51388 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq51308
  have eq51389 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq51388
  have eq51464 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq51389 eq29
    | exact resolve eq29 eq51389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq51389
  have eq51683 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq51464
    | exact resolve eq51464 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq51464
  have eq51806 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq51683 eq23623
    | exact resolve eq23623 eq51683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23623 eq51683
  have eq51957 : x = y := by grind
  clear eq51806
  have eq52090 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq51957
       grind)
    | exact superpose eq51957 eq19
    | exact resolve eq19 eq51957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq52091 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq51957
       grind)
    | exact superpose eq51957 eq25
    | exact resolve eq25 eq51957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq51957
  have eq52218 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq52091
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq52091
    | exact resolve eq52091 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq52091
  have eq52238 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq52218 eq27
    | exact resolve eq27 eq52218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq52218
  have eq52516 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq52238 eq79
    | exact resolve eq79 eq52238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq52238
  have eq52584 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq52516
       have i₂ := eq52090
       grind)
    | exact superpose eq52090 eq52516
    | exact resolve eq52516 eq52090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52090 eq52516
  have eq52611 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq52584 eq15
    | exact resolve eq15 eq52584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52584
  have eq52696 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq52611
    | exact resolve eq52611 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq52611
  have eq52717 : False := by grind
  exact eq52717

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxy_pxx_pyx_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
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
  have eq188 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (k X0 X0)
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq188
    | exact resolve eq188 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq196 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq189 X0 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq189
    | exact resolve eq189 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : y = (M.op (M.op x y) (k y y)) := by
    first
    | (have i₁ := eq189 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq189
    | (have j0 := eq189 y x
       grind)
    | exact resolve eq189 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq189
    | (have j0 := eq189 (σ y) (σ x)
       grind)
    | exact resolve eq189 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq208 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq196 X0
       have i₂ := eq174 (k X0 X0)
       grind)
    | exact superpose eq174 eq196
    | exact resolve eq196 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq210 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq202 eq16
    | exact resolve eq16 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq211 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq210 X0
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq210
    | exact resolve eq210 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq213 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq203 eq16
    | exact resolve eq16 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq214 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq213 X0
       have i₂ := eq174 sF4
       grind)
    | exact superpose eq174 eq213
    | exact resolve eq213 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq329 : (M.op x y) = (M.op (k y y) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq211 y
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq211
    | exact resolve eq211 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq334 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq214 sF3
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq214
    | exact resolve eq214 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq366 : ∀ X0 : G, (k y y) = (M.op (M.op X0 (M.op x y)) (M.op (k y y) (k y y))) := by
    intro X0
    first
    | exact superpose eq329 eq16
    | exact resolve eq16 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq367 : ∀ X0 : G, (k y y) = (M.op (M.op X0 (M.op x y)) (k (k y y) (k y y))) := by
    intro X0
    first
    | (have i₁ := eq366 X0
       have i₂ := eq174 (k y y)
       grind)
    | exact superpose eq174 eq366
    | exact resolve eq366 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq368 : ∀ X0 : G, (k y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq367 X0
       have i₂ := eq208 y
       grind)
    | exact superpose eq208 eq367
    | exact resolve eq367 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq370 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq334 eq16
    | exact resolve eq16 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq371 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq370 X0
       have i₂ := eq174 (k sF3 sF3)
       grind)
    | exact superpose eq174 eq370
    | exact resolve eq370 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq372 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq208 sF3
       grind)
    | exact superpose eq208 eq371
    | exact resolve eq371 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq416 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq418
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq418
    | exact resolve eq418 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq493 : (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq416
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq416
    | exact resolve eq416 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq571 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq571
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq571
    | exact resolve eq571 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq588 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq578
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq578
    | exact resolve eq578 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq1618 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq493
       grind)
    | exact superpose eq493 eq39
    | exact resolve eq39 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq1619 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1618
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1618
    | exact resolve eq1618 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618
  have eq1621 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq1619
    | exact resolve eq1619 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619
  have eq3717 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq1621 eq491
    | exact resolve eq491 eq1621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq3727 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq3717
       have r₂ := eq27
       grind)
    | exact resolve eq3717 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3717
  have eq3735 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq3727 eq588
    | (have r₁ := eq588
       have r₂ := eq3727
       grind)
    | exact resolve eq588 eq3727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq3741 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq3727 eq179
    | exact resolve eq179 eq3727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3727
  have eq3759 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq3735
  have eq3760 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq3759
  have eq3769 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq1621 eq3760
    | exact resolve eq3760 eq1621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621 eq3760
  have eq3775 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq3741 eq372
    | exact resolve eq372 eq3741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq3741
  have eq3789 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq26 eq3775
    | exact resolve eq3775 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3775
  have eq3793 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq3769 eq3789
    | exact resolve eq3789 eq3769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3769 eq3789
  have eq3795 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq3793
       have r₂ := eq27
       grind)
    | exact resolve eq3793 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3793
  have eq3806 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq179 x
       have i₂ := eq3795
       grind)
    | exact superpose eq3795 eq179
    | exact resolve eq179 eq3795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq3813 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq208 x
       have i₂ := eq3795
       grind)
    | exact superpose eq3795 eq208
    | exact resolve eq208 eq3795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3795
  have eq3845 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3806 eq368
    | exact resolve eq368 eq3806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq3806
  have eq3857 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3845
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3845
    | exact resolve eq3845 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3845
  have eq4030 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq208 y
       have i₂ := eq3857
       grind)
    | exact superpose eq3857 eq208
    | exact resolve eq208 eq3857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq3857
  have eq4044 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3813 eq4030
    | exact resolve eq4030 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3813 eq4030
  have eq4045 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq4044
  have eq4059 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq4045 eq31
    | exact resolve eq31 eq4045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4045
  have eq4120 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq4059
    | exact resolve eq4059 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4059
  have eq4121 : x = y := by grind
  clear eq4120
  have eq4124 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4121
       grind)
    | exact superpose eq4121 eq18
    | exact resolve eq18 eq4121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4125 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4121
       grind)
    | exact superpose eq4121 eq24
    | exact resolve eq24 eq4121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4121
  have eq4159 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4125
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4125
    | exact resolve eq4125 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4125
  have eq4160 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq4124
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq4124
    | exact resolve eq4124 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4124
  have eq4161 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4159 eq26
    | exact resolve eq26 eq4159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4159
  have eq4221 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4161
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq4161
    | exact resolve eq4161 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq4161
  have eq4231 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq4160
       grind)
    | exact superpose eq4160 eq39
    | exact resolve eq39 eq4160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq4160
  have eq4255 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4231
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4231
    | exact resolve eq4231 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4231
  have eq4263 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4221 eq4255
    | exact resolve eq4255 eq4221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4221 eq4255
  have eq4265 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4263
    | exact resolve eq4263 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4263
  have eq4267 : False := by grind
  exact eq4267
