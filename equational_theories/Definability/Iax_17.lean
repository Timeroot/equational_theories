import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3343`: `x ◇ y = y ◇ (x ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3343 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3343 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3343.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq19 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op X0 X0)
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq33 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq28
    | exact resolve eq28 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24
    | exact resolve eq24 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq19 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X0 (M.op X1 X0)
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq38
  have eq104 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq90
    | exact resolve eq90 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq178 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq30 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq30
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30 x y
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 x y
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq30 X0 X2
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 X0 X2
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X0
       have i₂ := eq58 (σ X0) X1
       grind)
    | (have i₁ := eq30 X0 X1
       have i₂ := eq58 (σ X1) (σ X0)
       grind)
    | exact superpose eq58 eq30
    | (have j1 := eq58 (σ X1) X0
       grind)
    | exact resolve eq30 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq732 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
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
  have eq810 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq732 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq732
    | (have j0 := eq732 X0 X1
       grind)
    | exact resolve eq732 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq872 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  clear eq810
  have eq1296 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq41 x y
       grind)
    | exact superpose eq41 eq14
    | (have j1 := eq41 x y
       grind)
    | exact resolve eq14 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1300 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq41 X0 X0
       grind)
    | exact superpose eq41 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq41 X0 X0
       grind)
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq1696 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq190
       have i₂ := eq872 y x
       grind)
    | exact superpose eq872 eq190
    | (have j1 := eq872 y x
       grind)
    | (have r₁ := eq190
       have r₂ := eq872 y x
       grind)
    | exact resolve eq190 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq872
  have eq1699 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq1696
  have eq2348 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq104 x
       have i₂ := eq1699
       grind)
    | exact superpose eq1699 eq104
    | exact resolve eq104 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq1699
  have eq2380 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq2348
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2348
    | exact resolve eq2348 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2348
  have eq2381 : x = (k x y) := by grind
  clear eq2380
  have eq5546 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq200 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq200
    | exact resolve eq200 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq5707 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5546 X0 X1 X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq5546
    | (have j0 := eq5546 X0 X1 X2
       grind)
    | exact resolve eq5546 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5546
  have eq47278 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5707 X2 (τ X1) (τ X0)
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq5707
    | (have j0 := eq5707 X2 (τ X1) X2
       grind)
    | exact resolve eq5707 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq5707
  have eq47890 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47278 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47278
    | (have j0 := eq47278 X0 X1 X2
       grind)
    | exact resolve eq47278 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47278
  have eq47947 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47890 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq47890
    | (have j0 := eq47890 X0 X1 X2
       grind)
    | exact resolve eq47890 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47890
  have eq47951 : ∀ X0 X1 X2 : G, (k X2 X1) = (M.op X2 X1) ∨ (k X0 X1) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47947 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47947
    | (have j0 := eq47947 X0 X1 X2
       grind)
    | exact resolve eq47947 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47947
  have eq70468 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1300 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq70534 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq70468 X0 X1
       have j1 := eq178 X1 X0
       grind)
    | (have r₁ := eq70468 (k X1 X1) X0
       have r₂ := eq178 X0 X1
       grind)
    | (have r₁ := eq70468 X0 (σ (k X1 X1))
       have r₂ := eq178 (σ X0) X1
       grind)
    | (have r₁ := eq70468 X1 X0
       have r₂ := eq178 X0 X1
       grind)
    | exact resolve eq70468 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq70468
  have eq70583 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq70534 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq70534 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq70534 eq16
    | (have j1 := eq70534 (τ X1) X0
       grind)
    | exact resolve eq16 eq70534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq70584 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq70534 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq70534 X0 (σ X0)
       grind)
    | exact superpose eq70534 eq9
    | (have j1 := eq70534 X1 X0
       grind)
    | exact resolve eq9 eq70534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70534
  have eq70629 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq70583 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq70583
    | (have j0 := eq70583 X0 X1
       grind)
    | exact resolve eq70583 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70583
  have eq70638 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq70629 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70629
    | (have j0 := eq70629 X0 X1
       grind)
    | exact resolve eq70629 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70629
  have eq71190 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1296
       have i₂ := eq70638 y x
       grind)
    | exact superpose eq70638 eq1296
    | (have j1 := eq70638 y x
       grind)
    | exact resolve eq1296 eq70638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296 eq70638
  have eq71326 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by grind
  clear eq71190
  have eq80343 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq70584 (σ X1) X0
       grind)
    | exact superpose eq70584 eq13
    | (have j1 := eq70584 (σ X1) X0
       grind)
    | exact resolve eq13 eq70584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70584
  have eq80362 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80343 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq80343
    | (have j0 := eq80343 X0 X1
       grind)
    | exact resolve eq80343 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80343
  have eq84314 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq80362 x y
       grind)
    | exact superpose eq80362 eq14
    | (have j1 := eq80362 x y
       grind)
    | exact resolve eq14 eq80362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80362
  have eq84364 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq84314
       have i₂ := eq2381
       grind)
    | exact superpose eq2381 eq84314
    | exact resolve eq84314 eq2381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2381 eq84314
  have eq84383 : y = (k x x) := by
    first
    | (have r₁ := eq84364
       have r₂ := eq71326
       grind)
    | exact resolve eq84364 eq71326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71326 eq84364
  have eq119407 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq312
    | exact resolve eq312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq120345 : ∀ X0 X1 : G, (M.op X1 X0) = (k (σ (τ X0)) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq119407 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq119407
    | (have j0 := eq119407 X0 X1
       grind)
    | exact resolve eq119407 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq119407
  have eq120347 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq120345 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq120345
    | (have j0 := eq120345 X0 X1
       grind)
    | exact resolve eq120345 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120345
  have eq165771 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 (M.op X0 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47951 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47951
  have eq165772 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq165771
  have eq165783 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq165772 X0 X0
       have i₂ := eq58 X0 X1
       grind)
    | (have i₁ := eq165772 X1 X0
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq165772
    | (have j0 := eq165772 X0 X1
       have j1 := eq58 X1 X0
       grind)
    | (have r₁ := eq165772 (M.op X0 X0) X0
       have r₂ := eq58 X0 (M.op X0 X0)
       grind)
    | exact resolve eq165772 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq165772
  have eq165958 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq165783 X0 X1
       have j1 := eq120347 X1 X0
       grind)
    | (have r₁ := eq165783 X1 X0
       have r₂ := eq120347 X0 X1
       grind)
    | exact resolve eq165783 eq120347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120347 eq165783
  have eq178572 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq165958 x x
       have i₂ := eq84383
       grind)
    | exact superpose eq84383 eq165958
    | exact resolve eq165958 eq84383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84383
  have eq178713 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq165958 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165958
  have eq178714 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq178713 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178713
  have eq178716 : y = (M.op x x) := by grind
  clear eq178572
  have eq179096 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq178714 (σ X0)
       grind)
    | exact superpose eq178714 eq13
    | exact resolve eq13 eq178714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179176 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq179096 X0
       have i₂ := eq178714 X0
       grind)
    | exact superpose eq178714 eq179096
    | exact resolve eq179096 eq178714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178714 eq179096
  have eq183834 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19 (σ X0)
       have i₂ := eq179176 X0
       grind)
    | exact superpose eq179176 eq19
    | exact resolve eq19 eq179176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183931 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq183834 X0
       have i₂ := eq179176 (M.op X0 X0)
       grind)
    | exact superpose eq179176 eq183834
    | exact resolve eq183834 eq179176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179176 eq183834
  have eq184008 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq183931 X0
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq183931
    | exact resolve eq183931 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq183931
  have eq208360 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq184008 x
       have i₂ := eq178716
       grind)
    | exact superpose eq178716 eq184008
    | exact resolve eq184008 eq178716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178716 eq184008
  have eq208409 : False := by grind
  exact eq208409

/-- `Equation3350`: `x ◇ y = y ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3350 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3350 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3350.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    grind
  have eq21 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq8 X0 X0 X1
       grind)
    | exact superpose eq8 eq20
    | exact resolve eq20 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq24 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24
    | exact resolve eq24 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq32 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X2 (M.op X1 X0)) ∨ (M.op X3 X0) = (k X3 X0) := by
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
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 X2))) = X0 ∨ (M.op (M.op X1 (M.op X2 X2)) X0) = (k (M.op X1 (M.op X2 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X1 (M.op X2 X2)) X2
       have i₂ := eq12 (M.op X1 (M.op X2 X2)) X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 (M.op X0 (M.op X2 X2)))
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X1 (M.op X2 X2)) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq38 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X0 ∨ (M.op (M.op X1 (M.op X2 X2)) X0) = (k (M.op X1 (M.op X2 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 X0 X1 X2
       have i₂ := eq8 X1 X1 X2
       grind)
    | exact superpose eq8 eq35
    | (have j0 := eq35 X0 X1 X2
       grind)
    | exact resolve eq35 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq41 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq46 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X2)) X3) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 (M.op X0 (M.op X2 X2)) X3
       have i₂ := eq8 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op (M.op X2 X2) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 (M.op (M.op X2 X2) X0) X3
       have i₂ := eq19 X2 X0 (M.op X1 X1)
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X0 X0) X1 X2
       have i₂ := eq19 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op (M.op X1 X1) X0) (M.op X0 (M.op (M.op X1 X1) X0))) := by
    intro X0 X1
    grind
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op (M.op X1 X1) X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq19 X1 X0 X0
       grind)
    | exact superpose eq19 eq61
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq66 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X2 X2) X0) X3) = (M.op X0 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq53 X0 x X2 X3
       have i₂ := eq8 X0 X3 x
       grind)
    | exact superpose eq8 eq53
    | exact resolve eq53 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq67 : ∀ X0 X2 X3 : G, (M.op (M.op X0 (M.op X2 X2)) X3) = (M.op X0 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq52 X0 x X2 X3
       have i₂ := eq8 X0 X3 x
       grind)
    | exact superpose eq8 eq52
    | exact resolve eq52 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq70 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27
    | exact resolve eq27 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq33 (τ X1) X0
       grind)
    | exact superpose eq33 eq17
    | (have j1 := eq33 (τ X1) X0
       grind)
    | exact resolve eq17 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq28 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq28
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq46
  have eq143 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq129 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq129
    | exact resolve eq129 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq163 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X3 X1) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X0 X1) X2
       have i₂ := eq32 X1 X0 (M.op X0 X1) X3
       grind)
    | exact superpose eq32 eq12
    | (have j0 := eq12 (M.op X0 X1) X2
       have j1 := eq32 X2 X1 X2 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq36 x y
       grind)
    | exact superpose eq36 eq14
    | (have j1 := eq36 x y
       grind)
    | exact resolve eq14 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq9
    | (have j1 := eq36 X0 X1
       grind)
    | exact resolve eq9 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq36 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X1
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq143
    | (have j1 := eq36 X1 X0
       grind)
    | exact resolve eq143 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq295 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq143 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq143 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq143
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq143 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq294 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq294
    | (have j0 := eq294 X0 X1
       grind)
    | exact resolve eq294 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq492 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 X2 (M.op X3 X3)
       have i₂ := eq58 X3 (M.op (M.op X1 X1) X2) X0
       grind)
    | (have i₁ := eq19 X1 X2 (M.op X3 X3)
       have i₂ := eq58 X0 (M.op (M.op X1 X1) X2) X3
       grind)
    | exact superpose eq58 eq19
    | exact resolve eq19 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X0 X0)) = (M.op X2 (M.op X3 X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq492 X3 x X2 X0
       have i₂ := eq19 x X2 (M.op X3 X3)
       grind)
    | exact superpose eq19 eq492
    | exact resolve eq492 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq549 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X3) = (k (M.op X1 X0) X3) ∨ (M.op X1 X1) = X3 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38 X0 X1 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq38 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X2)
       grind)
    | exact superpose eq12 eq38
    | (have j0 := eq38 X3 X1 X2
       have j1 := eq12 X1 X3
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (k (M.op X1 (M.op X2 X2)) X0) ∨ (M.op (M.op X1 (M.op X3 X3)) X0) = (k (M.op X1 (M.op X3 X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X1 X2
       have i₂ := eq38 X0 X1 X3
       grind)
    | (have i₁ := eq21 X0 X1
       have i₂ := eq38 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq38 eq21
    | (have j1 := eq38 X0 X1 X3
       grind)
    | exact resolve eq21 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq620 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (k (M.op X1 (M.op X3 X3)) X0) ∨ (M.op X1 (M.op X2 X2)) = (k (M.op X1 (M.op X2 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq572 X0 X1 X2 X3
       have i₂ := eq67 X1 X3 X0
       grind)
    | exact superpose eq67 eq572
    | (have j0 := eq572 X0 X1 X2 X3
       grind)
    | exact resolve eq572 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq699 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X3) = (k (M.op X0 (M.op X1 X1)) X3) ∨ (M.op (M.op (M.op X2 X2) X0) (M.op (M.op X2 X2) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38 X0 (M.op (M.op X2 X2) X0) X2
       have i₂ := eq66 X0 X2 (M.op X2 X2)
       grind)
    | exact superpose eq66 eq38
    | (have j0 := eq38 X3 (M.op (M.op X2 X2) X0) X2
       grind)
    | exact resolve eq38 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq703 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X1 (M.op (M.op X3 X3) X0)) ∨ (M.op X4 X2) = (k X4 X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq32 X2 X1 (M.op (M.op X3 X3) X0) X4
       have i₂ := eq66 X0 X3 (M.op X1 X2)
       grind)
    | exact superpose eq66 eq32
    | (have j0 := eq32 X2 X1 X2 X4
       grind)
    | exact resolve eq32 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq704 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = (M.op X2 (M.op (M.op X3 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X3 X0 (M.op (M.op X1 X1) X2)
       have i₂ := eq66 X2 X1 (M.op (M.op X3 X3) X0)
       grind)
    | exact superpose eq66 eq19
    | exact resolve eq19 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq710 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq704 X0 X1 X2 x
       have i₂ := eq19 x X0 X2
       grind)
    | exact superpose eq19 eq704
    | exact resolve eq704 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq711 : ∀ X0 X1 X2 X4 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) ∨ (M.op X4 X2) = (k X4 X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq703 X0 X1 X2 x X4
       have i₂ := eq19 x X0 X1
       grind)
    | exact superpose eq19 eq703
    | (have j0 := eq703 X0 X1 X2 x X4
       grind)
    | exact resolve eq703 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq715 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (k (M.op X0 (M.op X1 X1)) X3) ∨ (M.op (M.op (M.op X2 X2) X0) (M.op (M.op X2 X2) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq699 X0 X1 X2 X3
       have i₂ := eq67 X0 X1 X3
       grind)
    | exact superpose eq67 eq699
    | (have j0 := eq699 X0 X1 X2 X3
       grind)
    | exact resolve eq699 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq746 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 X2) X0)) = X3 ∨ (M.op X0 X3) = (k (M.op X0 (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq715 X0 X1 X2 X3
       have i₂ := eq19 X2 X0 (M.op (M.op X2 X2) X0)
       grind)
    | exact superpose eq19 eq715
    | (have j0 := eq715 X0 X1 X2 X3
       grind)
    | exact resolve eq715 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq752 : ∀ X0 X1 X3 : G, (M.op X0 X0) = X3 ∨ (M.op X0 X3) = (k (M.op X0 (M.op X1 X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq746 X0 X1 x X3
       have i₂ := eq19 x X0 X0
       grind)
    | exact superpose eq19 eq746
    | (have j0 := eq746 X0 X1 x X3
       grind)
    | exact resolve eq746 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq956 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (M.op X2 X2) X0
       have i₂ := eq497 (M.op X2 X2) X0 X1
       grind)
    | (have i₁ := eq19 X2 (M.op X2 X2) X0
       have i₂ := eq497 X1 X0 (M.op X2 X2)
       grind)
    | exact superpose eq497 eq19
    | exact resolve eq19 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1119 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 x X0 X1
       have i₂ := eq710 X1 x X0
       grind)
    | exact superpose eq710 eq19
    | exact resolve eq19 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1153 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X2) = (M.op X0 (M.op (M.op X3 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq67 X0 X1 (M.op (M.op X3 X3) X2)
       have i₂ := eq710 (M.op X0 (M.op X1 X1)) X3 X2
       grind)
    | exact superpose eq710 eq67
    | exact resolve eq67 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1154 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1153 X0 X1 X2 x
       have i₂ := eq19 x X2 X0
       grind)
    | exact superpose eq19 eq1153
    | exact resolve eq1153 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq1317 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85 X1 X0
       have i₂ := eq1119 X1 X0
       grind)
    | (have i₁ := eq85 X1 X0
       have i₂ := eq1119 X0 X1
       grind)
    | exact superpose eq1119 eq85
    | (have j0 := eq85 X1 X0
       grind)
    | exact resolve eq85 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1388 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ X1 ∨ (k X1 (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1317 (M.op X2 X2) X1
       have i₂ := eq58 X2 X1 X0
       grind)
    | (have i₁ := eq1317 (M.op X2 X2) X1
       have i₂ := eq58 X0 X1 X2
       grind)
    | exact superpose eq58 eq1317
    | (have j0 := eq1317 (M.op X0 X0) X1
       grind)
    | exact resolve eq1317 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1990 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq276 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq62 (M.op X0 X0) X0
       grind)
    | exact superpose eq62 eq276
    | (have j0 := eq276 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq276 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1994 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq276 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq276
    | (have j0 := eq276 (τ X0)
       grind)
    | exact resolve eq276 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq1996 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq1990 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990
  have eq1998 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1994 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1994
    | (have j0 := eq1994 X0
       grind)
    | exact resolve eq1994 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994
  have eq2002 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1998 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1998
    | (have j0 := eq1998 X0
       grind)
    | exact resolve eq1998 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998
  have eq2017 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2002 (τ X0)
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq2002
    | (have j0 := eq2002 (τ X0)
       grind)
    | exact resolve eq2002 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq2058 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq41
    | exact resolve eq41 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2134 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq10
    | (have j1 := eq41 X0 X1
       grind)
    | exact resolve eq10 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq2165 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2058 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2058
    | (have j0 := eq2058 X0 X1
       grind)
    | exact resolve eq2058 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058
  have eq2839 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq82
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq2888 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2839 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2839
    | (have j0 := eq2839 X0 X1
       grind)
    | exact resolve eq2839 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2839
  have eq4585 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq250
       have i₂ := eq2888 y x
       grind)
    | exact superpose eq2888 eq250
    | (have j1 := eq2888 y x
       grind)
    | (have r₁ := eq250
       have r₂ := eq2888 y x
       grind)
    | exact resolve eq250 eq2888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4586 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq250
       have i₂ := eq2165 y x
       grind)
    | exact superpose eq2165 eq250
    | (have j1 := eq2165 (σ y) (σ x)
       grind)
    | (have r₁ := eq250
       have r₂ := eq2165 y x
       grind)
    | exact resolve eq250 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq2165
  have eq4587 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq4586
  have eq4588 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq4585
  have eq5248 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq259 x x
       have i₂ := eq4587
       grind)
    | exact superpose eq4587 eq259
    | exact resolve eq259 eq4587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq4587
  have eq5288 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5248
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5248
    | exact resolve eq5248 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5248
  have eq5785 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq143 x
       have i₂ := eq4588
       grind)
    | exact superpose eq4588 eq143
    | exact resolve eq143 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq4588
  have eq5833 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq5785
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5785
    | exact resolve eq5785 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5785
  have eq5834 : x = (k x y) := by grind
  clear eq5833
  have eq12076 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq276 (τ X0)
       have i₂ := eq89 (τ X0) X0
       grind)
    | exact superpose eq89 eq276
    | (have j0 := eq276 (τ X0)
       have j1 := eq89 (τ X0) X0
       grind)
    | exact resolve eq276 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq12119 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq12076 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12076
    | (have j0 := eq12076 X0
       grind)
    | exact resolve eq12076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12076
  have eq12146 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq12119 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12119
    | (have j0 := eq12119 X0
       grind)
    | exact resolve eq12119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12119
  have eq12165 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq12146 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12146
    | (have j0 := eq12146 X0
       grind)
    | exact resolve eq12146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12146
  have eq12181 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12165 X0
       have j1 := eq85 X0 X0
       grind)
    | (have r₁ := eq12165 x
       have r₂ := eq85 x x
       grind)
    | exact resolve eq12165 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12165
  have eq12609 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12181 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq12181
    | (have j0 := eq12181 (σ X0)
       grind)
    | exact resolve eq12181 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12181
  have eq12643 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12609 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq12609
    | (have j0 := eq12609 X0
       grind)
    | exact resolve eq12609 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12609
  have eq19250 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq549 X1 X0 (M.op X0 X1) X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq19251 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq19250 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19250
  have eq19253 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19251 X0 X1
       have i₂ := eq1119 (M.op X0 X1) X1
       grind)
    | (have i₁ := eq19251 X0 X1
       have i₂ := eq1119 X1 (M.op X0 X1)
       grind)
    | exact superpose eq1119 eq19251
    | (have j0 := eq19251 X0 X1
       grind)
    | exact resolve eq19251 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19251
  have eq22378 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1119 (σ X1) (σ X0)
       have i₂ := eq314 X1 X0
       grind)
    | exact superpose eq314 eq1119
    | (have j1 := eq314 X1 X0
       grind)
    | exact resolve eq1119 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq27276 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 X2) ∨ (k (M.op X0 (M.op X1 X1)) X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq620 X2 X0 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq29122 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 (M.op X0 X1)) = X1 ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq163 X0 X1 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq29123 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq29122 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29122
  have eq29125 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29123 X0 X1
       have i₂ := eq1119 (M.op X0 X1) X1
       grind)
    | (have i₁ := eq29123 X0 X1
       have i₂ := eq1119 X1 (M.op X0 X1)
       grind)
    | exact superpose eq1119 eq29123
    | (have j0 := eq29123 X0 X1
       grind)
    | exact resolve eq29123 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29123
  have eq29374 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2017 (σ X0)
       have i₂ := eq295 (σ X0) X0
       grind)
    | exact superpose eq295 eq2017
    | (have j0 := eq2017 (σ X0)
       have j1 := eq295 (σ X0) X0
       grind)
    | exact resolve eq2017 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq29413 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq29374 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq29374
    | (have j0 := eq29374 X0
       grind)
    | exact resolve eq29374 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29374
  have eq29433 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq29413 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq29413
    | (have j0 := eq29413 X0
       grind)
    | exact resolve eq29413 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29413
  have eq29438 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq29433 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq29433
    | (have j0 := eq29433 X0
       grind)
    | exact resolve eq29433 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29433
  have eq29441 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq29438 X0
       have j1 := eq85 X0 X0
       grind)
    | (have r₁ := eq29438 x
       have r₂ := eq85 x x
       grind)
    | exact resolve eq29438 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq29438
  have eq30319 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq29441 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29441
    | (have j0 := eq29441 (τ X0)
       grind)
    | exact resolve eq29441 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29441
  have eq30387 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30319 X0
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq30319
    | (have j0 := eq30319 X0
       grind)
    | exact resolve eq30319 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30319
  have eq52008 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq5288
       grind)
    | exact superpose eq5288 eq9
    | exact resolve eq9 eq5288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5288
  have eq52102 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq52008
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq52008
    | exact resolve eq52008 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52008
  have eq53250 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33 x x
       have i₂ := eq52102
       grind)
    | exact superpose eq52102 eq33
    | exact resolve eq33 eq52102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq52102
  have eq53263 : y = (M.op x x) ∨ x = y := by grind
  clear eq53250
  have eq54515 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 y)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq8
    | exact resolve eq8 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54517 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y X0)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq19 x X0 X1
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq19
    | exact resolve eq19 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq54529 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 y) X1) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 x X1
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq67
    | exact resolve eq67 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq54560 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq497 X1 X0 x
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq497
    | exact resolve eq497 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54580 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op y X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq710 X0 x X1
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq710
    | exact resolve eq710 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq54582 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X0) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq956 X0 X1 x
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq956
    | exact resolve eq956 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54583 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op X0 y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq956 X0 x X1
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq956
    | exact resolve eq956 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq54591 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 y) X0) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1154 X1 x X0
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq1154
    | exact resolve eq1154 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55630 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k (M.op X0 y) (M.op X2 X2)) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1388 X1 (M.op X0 y) X2
       have i₂ := eq54515 X0 (M.op X1 X1)
       grind)
    | exact superpose eq54515 eq1388
    | (have j0 := eq1388 X0 (M.op X0 y) X2
       grind)
    | exact resolve eq1388 eq54515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388 eq54515
  have eq55665 : ∀ X0 X2 : G, (M.op X0 y) = (k (M.op X0 y) (M.op X2 X2)) ∨ x = y := by
    intro X0 X2
    first
    | (have j0 := eq55630 X0 x X2
       grind)
    | (have r₁ := eq55630 X0 x X2
       have r₂ := eq54560 X0 x
       grind)
    | exact resolve eq55630 eq54560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54560 eq55630
  have eq76964 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op X1 y) X0) ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq54580 (M.op X1 y) X0
       have i₂ := eq54591 (M.op y X0) X1
       grind)
    | exact superpose eq54591 eq54580
    | exact resolve eq54580 eq54591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54580
  have eq76983 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op X1 y) X0) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq76964 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76964
  have eq86147 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 y) y) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq55665 X0 x
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq55665
    | exact resolve eq55665 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55665
  have eq86182 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 y) y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq86147 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86147
  have eq92106 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op X1 (M.op X2 X2)) ∨ (M.op X3 X0) = (k (M.op X3 (M.op X4 X4)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq497 X2 X1 X3
       have i₂ := eq752 X3 X4 X0
       grind)
    | (have i₁ := eq497 X0 X2 X3
       have i₂ := eq752 X0 X1 (M.op X3 X3)
       grind)
    | exact superpose eq752 eq497
    | (have j1 := eq752 X3 X4 X0
       grind)
    | exact resolve eq497 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq92820 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq2134 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2134
  have eq92821 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq92820 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92820
    | (have j0 := eq92820 X0
       grind)
    | exact resolve eq92820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92820
  have eq94787 : (M.op x y) = (k y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq19253 x x
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq19253
    | exact resolve eq19253 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19253 eq53263
  have eq94913 : (M.op x y) = (k y x) ∨ x = y := by grind
  clear eq94787
  have eq108683 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X0 y) (M.op X1 X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1154 y X1 X0
       have i₂ := eq76983 (M.op X1 X1) X0
       grind)
    | exact superpose eq76983 eq1154
    | exact resolve eq1154 eq76983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154 eq76983
  have eq136261 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq22378 y x
       grind)
    | exact superpose eq22378 eq14
    | (have j1 := eq22378 y x
       grind)
    | exact resolve eq14 eq22378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22378
  have eq136433 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq136261
       have i₂ := eq94913
       grind)
    | exact superpose eq94913 eq136261
    | exact resolve eq136261 eq94913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94913
  have eq136434 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq136261
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq136261
    | (have j1 := eq12 y x
       grind)
    | exact resolve eq136261 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136437 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq136261
       have i₂ := eq2888 x y
       grind)
    | exact superpose eq2888 eq136261
    | (have j1 := eq2888 x y
       grind)
    | exact resolve eq136261 eq2888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2888 eq136261
  have eq136439 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k y x) := by grind
  clear eq136437
  have eq136440 : y = (M.op x y) ∨ x = y := by grind
  clear eq136433
  have eq136441 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq136439
       have i₂ := eq1119 y x
       grind)
    | (have i₁ := eq136439
       have i₂ := eq1119 x y
       grind)
    | exact superpose eq1119 eq136439
    | exact resolve eq136439 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136439
  have eq136442 : y = (k y x) := by grind
  clear eq136441
  have eq136446 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq136434
       have i₂ := eq1119 y x
       grind)
    | (have i₁ := eq136434
       have i₂ := eq1119 x y
       grind)
    | exact superpose eq1119 eq136434
    | exact resolve eq136434 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136434
  have eq136447 : y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq136446
  have eq136448 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq136447
       have i₂ := eq1119 y x
       grind)
    | (have i₁ := eq136447
       have i₂ := eq1119 x y
       grind)
    | exact superpose eq1119 eq136447
    | exact resolve eq136447 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136447
  have eq136565 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq54529 x X0
       have i₂ := eq136440
       grind)
    | exact superpose eq136440 eq54529
    | exact resolve eq54529 eq136440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54529
  have eq136584 : y = (k y y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq86182 x
       have i₂ := eq136440
       grind)
    | exact superpose eq136440 eq86182
    | exact resolve eq86182 eq136440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86182
  have eq136596 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq108683 x x
       have i₂ := eq136440
       grind)
    | exact superpose eq136440 eq108683
    | exact resolve eq108683 eq136440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108683 eq136440
  have eq136645 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq136596 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136596
  have eq136657 : y = (k y y) ∨ x = y := by grind
  clear eq136584
  have eq136676 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq136565 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136565
  have eq136722 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq276 y
       have i₂ := eq136657
       grind)
    | exact superpose eq136657 eq276
    | (have j0 := eq276 y
       grind)
    | exact resolve eq276 eq136657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq136730 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) ∨ x = y := by
    first
    | (have i₁ := eq2017 y
       have i₂ := eq136657
       grind)
    | exact superpose eq136657 eq2017
    | (have j0 := eq2017 y
       grind)
    | exact resolve eq2017 eq136657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2017
  have eq136742 : y ≠ y ∨ y = (σ (M.op (τ y) (τ y))) ∨ x = y := by
    first
    | (have i₁ := eq92821 y
       have i₂ := eq136657
       grind)
    | exact superpose eq136657 eq92821
    | (have j0 := eq92821 y
       grind)
    | (have r₁ := eq92821 y
       have r₂ := eq136657
       grind)
    | exact resolve eq92821 eq136657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92821 eq136657
  have eq136754 : y = (σ (M.op (τ y) (τ y))) ∨ x = y := by grind
  clear eq136742
  have eq136757 : (τ y) = (M.op (τ y) (τ y)) ∨ x = y := by grind
  clear eq136730
  have eq136760 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq136722
  have eq137445 : y = (M.op y x) ∨ (k x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29125 y y
       have i₂ := eq136448
       grind)
    | exact superpose eq136448 eq29125
    | exact resolve eq29125 eq136448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29125 eq136448
  have eq137448 : y = (M.op x y) ∨ (k x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq137445
       have i₂ := eq1119 y x
       grind)
    | (have i₁ := eq137445
       have i₂ := eq1119 x y
       grind)
    | exact superpose eq1119 eq137445
    | exact resolve eq137445 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137445
  have eq137449 : y = (M.op x y) ∨ (k x y) = (M.op y x) := by grind
  clear eq137448
  have eq137481 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq137449
       have i₂ := eq1119 y x
       grind)
    | (have i₁ := eq137449
       have i₂ := eq1119 x y
       grind)
    | exact superpose eq1119 eq137449
    | exact resolve eq137449 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137449
  have eq137488 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq137481
       have i₂ := eq5834
       grind)
    | exact superpose eq5834 eq137481
    | exact resolve eq137481 eq5834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5834 eq137481
  have eq137715 : ∀ X0 : G, (M.op y X0) = (M.op X0 x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq54591 X0 x
       have i₂ := eq137488
       grind)
    | exact superpose eq137488 eq54591
    | exact resolve eq54591 eq137488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54591
  have eq137775 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq137488
  have eq137818 : ∀ X0 : G, (M.op y X0) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq137715 X0
       grind)
    | (have r₁ := eq137715 X0
       have r₂ := eq137775
       grind)
    | exact resolve eq137715 eq137775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137715
  have eq141917 : ∀ X0 : G, y = (M.op x (M.op X0 X0)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq136676 (M.op X0 X0)
       have i₂ := eq136645 X0
       grind)
    | exact superpose eq136645 eq136676
    | exact resolve eq136676 eq136645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141970 : ∀ X0 X1 : G, y = (M.op y X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq711 y X0 X0 X1
       have i₂ := eq136645 X0
       grind)
    | exact superpose eq136645 eq711
    | (have j0 := eq711 X0 X1 X0 X1
       grind)
    | exact resolve eq711 eq136645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq142046 : ∀ X0 : G, y = (M.op x (M.op X0 X0)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq141917 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141917
  have eq143826 : (τ (τ y)) ≠ (τ (τ y)) ∨ (τ (τ y)) = (τ (k (τ y) (τ y))) ∨ x = y := by
    first
    | (have i₁ := eq30387 (τ y)
       have i₂ := eq136757
       grind)
    | exact superpose eq136757 eq30387
    | (have j0 := eq30387 (τ y)
       grind)
    | exact resolve eq30387 eq136757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30387
  have eq143832 : ∀ X0 : G, (M.op X0 y) = (M.op (τ y) X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq54583 X0 (τ y)
       have i₂ := eq136757
       grind)
    | exact superpose eq136757 eq54583
    | exact resolve eq54583 eq136757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143857 : y = (M.op y (τ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq136645 (τ y)
       have i₂ := eq136757
       grind)
    | exact superpose eq136757 eq136645
    | exact resolve eq136645 eq136757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143878 : y = (M.op y (τ y)) ∨ x = y := by grind
  clear eq143857
  have eq143900 : ∀ X0 : G, (M.op X0 y) = (M.op (τ y) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq143832 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143832
  have eq143906 : (τ (τ y)) = (τ (k (τ y) (τ y))) ∨ x = y := by grind
  clear eq143826
  have eq143923 : (τ (τ (k y y))) = (τ (τ y)) ∨ x = y := by
    first
    | (have i₁ := eq143906
       have i₂ := eq70 y y
       grind)
    | exact superpose eq70 eq143906
    | exact resolve eq143906 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq143906
  have eq144398 : (σ (σ y)) ≠ (σ (σ y)) ∨ (σ (σ y)) = (σ (k (σ y) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq12643 (σ y)
       have i₂ := eq136760
       grind)
    | exact superpose eq136760 eq12643
    | (have j0 := eq12643 (σ y)
       grind)
    | exact resolve eq12643 eq136760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12643
  have eq144409 : ∀ X0 : G, (M.op y X0) = (M.op X0 (σ y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq54582 X0 (σ y)
       have i₂ := eq136760
       grind)
    | exact superpose eq136760 eq54582
    | exact resolve eq54582 eq136760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54582
  have eq144410 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq54583 X0 (σ y)
       have i₂ := eq136760
       grind)
    | exact superpose eq136760 eq54583
    | exact resolve eq54583 eq136760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54583
  have eq144435 : y = (M.op y (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq136645 (σ y)
       have i₂ := eq136760
       grind)
    | exact superpose eq136760 eq136645
    | exact resolve eq136645 eq136760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144456 : y = (M.op y (σ y)) ∨ x = y := by grind
  clear eq144435
  have eq144478 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq144410 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144410
  have eq144479 : ∀ X0 : G, (M.op y X0) = (M.op X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq144409 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144409
  have eq144485 : (σ (σ y)) = (σ (k (σ y) (σ y))) ∨ x = y := by grind
  clear eq144398
  have eq144504 : (σ (σ y)) = (σ (σ (k y y))) ∨ x = y := by
    first
    | (have i₁ := eq144485
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq144485
    | exact resolve eq144485 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144485
  have eq144811 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 X3) ∨ (M.op X0 X3) = (k (M.op X0 (M.op X1 X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq27276 x X0 x
       have i₂ := eq497 X0 x X3
       grind)
    | (have i₁ := eq27276 x X3 x
       have i₂ := eq497 X0 x X3
       grind)
    | exact superpose eq497 eq27276
    | (have j0 := eq27276 X0 X1 X3
       grind)
    | (have r₁ := eq27276 x X0 (M.op X3 X3)
       have r₂ := eq497 X0 x X3
       grind)
    | (have r₁ := eq27276 x X3 (M.op X0 X0)
       have r₂ := eq497 X0 x X3
       grind)
    | exact resolve eq27276 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq144826 : ∀ X1 : G, y ≠ (M.op y X1) ∨ (M.op y X1) = (k y X1) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq27276 y x x
       have i₂ := eq136645 x
       grind)
    | exact superpose eq136645 eq27276
    | exact resolve eq27276 eq136645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27276 eq136645
  have eq144838 : ∀ X1 : G, (M.op y X1) = (k y X1) ∨ x = y := by
    intro X1
    first
    | (have j0 := eq144826 X1
       have j1 := eq141970 X1 y
       grind)
    | (have r₁ := eq144826 x
       have r₂ := eq141970 x X1
       grind)
    | exact resolve eq144826 eq141970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141970 eq144826
  have eq144839 : ∀ X0 X1 X3 : G, (M.op X0 X3) = (k (M.op X0 (M.op X1 X1)) X3) := by
    intro X0 X1 X3
    first
    | (have j0 := eq144811 X0 X1 X3
       have j1 := eq92106 X3 X1 x X0 X1
       grind)
    | (have r₁ := eq144811 X1 X1 (M.op x x)
       have r₂ := eq92106 (M.op X1 X1) X1 x X3 x
       grind)
    | (have r₁ := eq144811 X1 x X0
       have r₂ := eq92106 X0 X1 x X3 x
       grind)
    | exact resolve eq144811 eq92106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92106 eq144811
  have eq145526 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op y X0) X1) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq144839 X0 y X1
       have i₂ := eq54517 y X0
       grind)
    | exact superpose eq54517 eq144839
    | exact resolve eq144839 eq54517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54517
  have eq145611 : ∀ X0 : G, (M.op x X0) = (k y X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq144839 x x X0
       have i₂ := eq142046 x
       grind)
    | exact superpose eq142046 eq144839
    | exact resolve eq144839 eq142046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142046 eq144839
  have eq146567 : (τ y) = (M.op (τ y) y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq136757
       have i₂ := eq143900 (τ y)
       grind)
    | exact superpose eq143900 eq136757
    | exact resolve eq136757 eq143900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136757
  have eq146568 : y = (σ (M.op (τ y) y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq136754
       have i₂ := eq143900 (τ y)
       grind)
    | exact superpose eq143900 eq136754
    | exact resolve eq136754 eq143900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146571 : y = (k y (σ (M.op (τ y) y))) ∨ x = y := by
    first
    | (have i₁ := eq28 y
       have i₂ := eq143900 (τ y)
       grind)
    | exact superpose eq143900 eq28
    | exact resolve eq28 eq143900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq143900
  have eq146903 : y = (σ (M.op (τ y) y)) ∨ x = y := by grind
  clear eq146568
  have eq146904 : (τ y) = (M.op (τ y) y) ∨ x = y := by grind
  clear eq146567
  have eq147073 : y = (k y (σ (M.op y (τ y)))) ∨ x = y := by
    first
    | (have i₁ := eq146571
       have i₂ := eq1119 (τ y) y
       grind)
    | (have i₁ := eq146571
       have i₂ := eq1119 y (τ y)
       grind)
    | exact superpose eq1119 eq146571
    | exact resolve eq146571 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146571
  have eq147075 : y = (σ (M.op y (τ y))) ∨ x = y := by
    first
    | (have i₁ := eq146903
       have i₂ := eq1119 (τ y) y
       grind)
    | (have i₁ := eq146903
       have i₂ := eq1119 y (τ y)
       grind)
    | exact superpose eq1119 eq146903
    | exact resolve eq146903 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146903
  have eq147076 : (τ y) = (M.op y (τ y)) ∨ x = y := by
    first
    | (have i₁ := eq146904
       have i₂ := eq1119 (τ y) y
       grind)
    | (have i₁ := eq146904
       have i₂ := eq1119 y (τ y)
       grind)
    | exact superpose eq1119 eq146904
    | exact resolve eq146904 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146904
  have eq147155 : y = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq147075
       have i₂ := eq143878
       grind)
    | exact superpose eq143878 eq147075
    | exact resolve eq147075 eq143878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147196 : y = (σ y) ∨ x = y := by grind
  clear eq147155
  have eq147200 : (σ (M.op x y)) ≠ (M.op (σ x) y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq147196
       grind)
    | exact superpose eq147196 eq14
    | exact resolve eq14 eq147196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147223 : y = (τ y) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq147196
       grind)
    | exact superpose eq147196 eq9
    | exact resolve eq9 eq147196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147224 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq147196
       grind)
    | exact superpose eq147196 eq13
    | exact resolve eq13 eq147196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147279 : (σ (M.op x y)) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq147200
       have i₂ := eq1119 (σ x) y
       grind)
    | (have i₁ := eq147200
       have i₂ := eq1119 y (σ x)
       grind)
    | exact superpose eq1119 eq147200
    | exact resolve eq147200 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147200
  have eq147290 : y = (σ (M.op y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq147075
       have i₂ := eq147223
       grind)
    | exact superpose eq147223 eq147075
    | exact resolve eq147075 eq147223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147075 eq147223
  have eq147319 : y = (σ (M.op y y)) ∨ x = y := by grind
  clear eq147290
  have eq147350 : (M.op y y) = (τ y) ∨ x = y := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq147319
       grind)
    | exact superpose eq147319 eq9
    | exact resolve eq9 eq147319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148327 : (τ y) = (M.op x (τ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq136676 (τ y)
       have i₂ := eq147076
       grind)
    | exact superpose eq147076 eq136676
    | exact resolve eq136676 eq147076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136676
  have eq148347 : (τ y) = (M.op x (τ y)) ∨ x = y := by grind
  clear eq148327
  have eq148452 : (τ y) ≠ (τ y) ∨ (τ y) = (k (τ y) x) ∨ x = y := by
    first
    | (have i₁ := eq1317 x (τ y)
       have i₂ := eq148347
       grind)
    | exact superpose eq148347 eq1317
    | (have j0 := eq1317 x (τ y)
       grind)
    | (have r₁ := eq1317 x (τ y)
       have r₂ := eq148347
       grind)
    | exact resolve eq1317 eq148347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317 eq148347
  have eq148456 : (τ y) = (k (τ y) x) ∨ x = y := by grind
  clear eq148452
  have eq148472 : (σ (τ y)) = (k y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq16 y x
       have i₂ := eq148456
       grind)
    | exact superpose eq148456 eq16
    | exact resolve eq16 eq148456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq148456
  have eq148482 : y = (k y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq148472
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq148472
    | exact resolve eq148472 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148472
  have eq148497 : y = (M.op y (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq144838 (σ x)
       have i₂ := eq148482
       grind)
    | exact superpose eq148482 eq144838
    | exact resolve eq144838 eq148482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144838 eq148482
  have eq148511 : y = (M.op y (σ x)) ∨ x = y := by grind
  clear eq148497
  have eq150436 : (σ y) = (M.op (σ y) y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq136760
       have i₂ := eq144478 (σ y)
       grind)
    | exact superpose eq144478 eq136760
    | exact resolve eq136760 eq144478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136760 eq144478
  have eq150767 : (σ y) = (M.op (σ y) y) ∨ x = y := by grind
  clear eq150436
  have eq150940 : (σ y) = (M.op y (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq150767
       have i₂ := eq1119 (σ y) y
       grind)
    | (have i₁ := eq150767
       have i₂ := eq1119 y (σ y)
       grind)
    | exact superpose eq1119 eq150767
    | exact resolve eq150767 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150767
  have eq151682 : (σ y) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq150940
       have i₂ := eq144479 y
       grind)
    | exact superpose eq144479 eq150940
    | exact resolve eq150940 eq144479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144479 eq150940
  have eq151766 : (σ y) = (M.op y y) ∨ x = y := by grind
  clear eq151682
  have eq151954 : (σ y) = (τ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq147350
       have i₂ := eq151766
       grind)
    | exact superpose eq151766 eq147350
    | exact resolve eq147350 eq151766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147350 eq151766
  have eq152260 : (σ y) = (τ y) ∨ x = y := by grind
  clear eq151954
  have eq152370 : y = (σ (M.op (σ y) (σ y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq136754
       have i₂ := eq152260
       grind)
    | exact superpose eq152260 eq136754
    | exact resolve eq136754 eq152260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136754 eq152260
  have eq152430 : y = (σ (M.op (σ y) (σ y))) ∨ x = y := by grind
  clear eq152370
  have eq167630 : (τ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq9 (M.op (σ y) (σ y))
       have i₂ := eq152430
       grind)
    | exact superpose eq152430 eq9
    | exact resolve eq9 eq152430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169524 : y = (σ (M.op y x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq147319
       have i₂ := eq137818 y
       grind)
    | exact superpose eq137818 eq147319
    | exact resolve eq147319 eq137818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147319
  have eq169890 : y = (σ (M.op y x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq169524
       have r₂ := eq137775
       grind)
    | exact resolve eq169524 eq137775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169524
  have eq170066 : y = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq169890
       have i₂ := eq1119 y x
       grind)
    | (have i₁ := eq169890
       have i₂ := eq1119 x y
       grind)
    | exact superpose eq1119 eq169890
    | exact resolve eq169890 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169890
  have eq173278 : ∀ X0 : G, (M.op (σ x) X0) = (k y X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq145526 (σ x) X0
       have i₂ := eq148511
       grind)
    | exact superpose eq148511 eq145526
    | exact resolve eq145526 eq148511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148511
  have eq173283 : ∀ X0 : G, (M.op (σ y) X0) = (k y X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq145526 (σ y) X0
       have i₂ := eq144456
       grind)
    | exact superpose eq144456 eq145526
    | exact resolve eq145526 eq144456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144456
  have eq173292 : ∀ X0 : G, (k (τ y) X0) = (M.op (τ y) X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq145526 (τ y) X0
       have i₂ := eq147076
       grind)
    | exact superpose eq147076 eq145526
    | exact resolve eq145526 eq147076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147076
  have eq173293 : ∀ X0 : G, (k y X0) = (M.op (τ y) X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq145526 (τ y) X0
       have i₂ := eq143878
       grind)
    | exact superpose eq143878 eq145526
    | exact resolve eq145526 eq143878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143878 eq145526
  have eq173461 : ∀ X0 : G, (k y X0) = (M.op (τ y) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq173293 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173293
  have eq173462 : ∀ X0 : G, (k (τ y) X0) = (M.op (τ y) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq173292 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173292
  have eq173471 : ∀ X0 : G, (M.op (σ y) X0) = (k y X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq173283 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173283
  have eq173476 : ∀ X0 : G, (M.op (σ x) X0) = (k y X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq173278 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173278
  have eq173684 : ∀ X0 : G, (k y X0) = (M.op X0 (τ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1119 X0 (τ y)
       have i₂ := eq173461 X0
       grind)
    | exact superpose eq173461 eq1119
    | exact resolve eq1119 eq173461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173461
  have eq174876 : (τ y) = (k y (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq167630
       have i₂ := eq173471 (σ y)
       grind)
    | exact superpose eq173471 eq167630
    | exact resolve eq167630 eq173471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167630
  have eq174877 : y = (σ (k y (σ y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq152430
       have i₂ := eq173471 (σ y)
       grind)
    | exact superpose eq173471 eq152430
    | exact resolve eq152430 eq173471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152430 eq173471
  have eq175200 : y = (σ (k y (σ y))) ∨ x = y := by grind
  clear eq174877
  have eq175201 : (τ y) = (k y (σ y)) ∨ x = y := by grind
  clear eq174876
  have eq175303 : y = (σ (k y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq175200
       have i₂ := eq147196
       grind)
    | exact superpose eq147196 eq175200
    | exact resolve eq175200 eq147196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147196 eq175200
  have eq175334 : y = (σ (k y y)) ∨ x = y := by grind
  clear eq175303
  have eq175366 : (k y y) = (τ y) ∨ x = y := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq175334
       grind)
    | exact superpose eq175334 eq9
    | exact resolve eq9 eq175334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175334
  have eq175492 : (τ (τ y)) = (k (τ y) y) ∨ x = y := by
    first
    | (have i₁ := eq27 y y
       have i₂ := eq175201
       grind)
    | exact superpose eq175201 eq27
    | exact resolve eq27 eq175201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq175201
  have eq179327 : ∀ X0 : G, (M.op X0 (σ x)) = (k y X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1119 X0 (σ x)
       have i₂ := eq173476 X0
       grind)
    | exact superpose eq173476 eq1119
    | exact resolve eq1119 eq173476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179410 : (k y x) = (M.op y (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq137818 (σ x)
       have i₂ := eq173476 x
       grind)
    | exact superpose eq173476 eq137818
    | exact resolve eq137818 eq173476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137818 eq173476
  have eq179626 : (k y x) = (M.op y (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq179410
       have r₂ := eq137775
       grind)
    | exact resolve eq179410 eq137775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179410
  have eq179668 : y = (M.op y (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq179626
       have i₂ := eq136442
       grind)
    | exact superpose eq136442 eq179626
    | exact resolve eq179626 eq136442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136442 eq179626
  have eq215538 : (τ (τ y)) = (τ (τ (τ y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq143923
       have i₂ := eq175366
       grind)
    | exact superpose eq175366 eq143923
    | exact resolve eq143923 eq175366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143923 eq175366
  have eq215561 : (τ (τ y)) = (τ (τ (τ y))) ∨ x = y := by grind
  clear eq215538
  have eq225677 : y = (k y (σ (k y y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq147073
       have i₂ := eq173684 y
       grind)
    | exact superpose eq173684 eq147073
    | exact resolve eq147073 eq173684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147073
  have eq225705 : y = (k y (σ (k y y))) ∨ x = y := by grind
  clear eq225677
  have eq239185 : (τ (τ y)) = (M.op (τ y) y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq175492
       have i₂ := eq173462 y
       grind)
    | exact superpose eq173462 eq175492
    | exact resolve eq175492 eq173462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173462 eq175492
  have eq239201 : (τ (τ y)) = (M.op (τ y) y) ∨ x = y := by grind
  clear eq239185
  have eq239227 : (τ (τ y)) = (M.op y (τ y)) ∨ x = y := by
    first
    | (have i₁ := eq239201
       have i₂ := eq1119 (τ y) y
       grind)
    | (have i₁ := eq239201
       have i₂ := eq1119 y (τ y)
       grind)
    | exact superpose eq1119 eq239201
    | exact resolve eq239201 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119 eq239201
  have eq239587 : (k y y) = (τ (τ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq173684 y
       have i₂ := eq239227
       grind)
    | exact superpose eq239227 eq173684
    | exact resolve eq173684 eq239227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173684 eq239227
  have eq239598 : (k y y) = (τ (τ y)) ∨ x = y := by grind
  clear eq239587
  have eq239676 : (k y y) = (τ (k y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq215561
       have i₂ := eq239598
       grind)
    | exact superpose eq239598 eq215561
    | exact resolve eq215561 eq239598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215561
  have eq239686 : (k y y) = (τ (k y y)) ∨ x = y := by grind
  clear eq239676
  have eq240053 : (k y y) = (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq239686
       grind)
    | exact superpose eq239686 eq10
    | exact resolve eq10 eq239686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239686
  have eq240294 : (σ (k y y)) = (σ (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq144504
       have i₂ := eq240053
       grind)
    | exact superpose eq240053 eq144504
    | exact resolve eq144504 eq240053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144504
  have eq240314 : (σ (k y y)) = (σ (σ y)) ∨ x = y := by grind
  clear eq240294
  have eq240565 : (k y y) = (σ (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq240053
       have i₂ := eq240314
       grind)
    | exact superpose eq240314 eq240053
    | exact resolve eq240053 eq240314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240053 eq240314
  have eq240575 : (k y y) = (σ (σ y)) ∨ x = y := by grind
  clear eq240565
  have eq243825 : y = (σ (k y (k y y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq225705
       have i₂ := eq147224 (k y y)
       grind)
    | exact superpose eq147224 eq225705
    | exact resolve eq225705 eq147224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225705
  have eq243874 : y = (σ (k y (k y y))) ∨ x = y := by grind
  clear eq243825
  have eq244203 : (τ y) = (k y (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq9 (k y (k y y))
       have i₂ := eq243874
       grind)
    | exact superpose eq243874 eq9
    | exact resolve eq9 eq243874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243874
  have eq244543 : (τ y) = (k y (σ (σ y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq244203
       have i₂ := eq240575
       grind)
    | exact superpose eq240575 eq244203
    | exact resolve eq244203 eq240575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240575 eq244203
  have eq244633 : (τ y) = (k y (σ (σ y))) ∨ x = y := by grind
  clear eq244543
  have eq248098 : (τ y) = (σ (k y (σ y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq147224 (σ y)
       have i₂ := eq244633
       grind)
    | exact superpose eq244633 eq147224
    | exact resolve eq147224 eq244633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244633
  have eq248142 : (τ y) = (σ (k y (σ y))) ∨ x = y := by grind
  clear eq248098
  have eq248631 : (k y (σ y)) = (τ (τ y)) ∨ x = y := by
    first
    | (have i₁ := eq9 (k y (σ y))
       have i₂ := eq248142
       grind)
    | exact superpose eq248142 eq9
    | exact resolve eq9 eq248142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248142
  have eq248810 : (σ (k y y)) = (τ (τ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq147224 y
       have i₂ := eq248631
       grind)
    | exact superpose eq248631 eq147224
    | exact resolve eq147224 eq248631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147224 eq248631
  have eq248854 : (σ (k y y)) = (τ (τ y)) ∨ x = y := by grind
  clear eq248810
  have eq249297 : (σ (M.op x y)) = (τ (τ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq248854
       have i₂ := eq145611 y
       grind)
    | exact superpose eq145611 eq248854
    | exact resolve eq248854 eq145611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145611 eq248854
  have eq249362 : (σ (M.op x y)) = (τ (τ y)) ∨ x = y := by grind
  clear eq249297
  have eq250126 : (M.op x y) = (τ (τ (τ y))) ∨ x = y := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq249362
       grind)
    | exact superpose eq249362 eq9
    | exact resolve eq9 eq249362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249362
  have eq250420 : (M.op x y) = (τ (k y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq250126
       have i₂ := eq239598
       grind)
    | exact superpose eq239598 eq250126
    | exact resolve eq250126 eq239598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239598 eq250126
  have eq250446 : (M.op x y) = (τ (k y y)) ∨ x = y := by grind
  clear eq250420
  have eq250667 : (σ (M.op x y)) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq250446
       grind)
    | exact superpose eq250446 eq10
    | exact resolve eq10 eq250446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250446
  have eq256762 : y ≠ (M.op y (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq147279
       have i₂ := eq170066
       grind)
    | exact superpose eq170066 eq147279
    | exact resolve eq147279 eq170066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170066
  have eq256770 : (k y y) ≠ (M.op y (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq147279
       have i₂ := eq250667
       grind)
    | exact superpose eq250667 eq147279
    | exact resolve eq147279 eq250667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147279 eq250667
  have eq256771 : (k y y) ≠ (M.op y (σ x)) ∨ x = y := by grind
  clear eq256770
  have eq256785 : x = y := by
    first
    | (have r₁ := eq256771
       have r₂ := eq179327 y
       grind)
    | exact resolve eq256771 eq179327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179327 eq256771
  have eq256790 : y ≠ (M.op y (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq256762
       have r₂ := eq137775
       grind)
    | exact resolve eq256762 eq137775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137775 eq256762
  have eq256795 : x = (M.op x y) := by
    first
    | (have r₁ := eq256790
       have r₂ := eq179668
       grind)
    | exact resolve eq256790 eq179668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179668 eq256790
  have eq256797 : x = (M.op x x) := by
    first
    | (have i₁ := eq256795
       have i₂ := eq256785
       grind)
    | exact superpose eq256785 eq256795
    | exact resolve eq256795 eq256785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256795
  have eq256798 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq256785
       grind)
    | exact superpose eq256785 eq14
    | exact resolve eq14 eq256785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256785
  have eq256929 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq256798
       have i₂ := eq256797
       grind)
    | exact superpose eq256797 eq256798
    | exact resolve eq256798 eq256797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256798
  have eq257051 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq1996 x
       have i₂ := eq256797
       grind)
    | exact superpose eq256797 eq1996
    | exact resolve eq1996 eq256797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996
  have eq257181 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq257051
       have i₂ := eq256797
       grind)
    | exact superpose eq256797 eq257051
    | exact resolve eq257051 eq256797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256797 eq257051
  have eq257191 : False := by grind
  exact eq257191

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3352 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3352 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq93 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq89 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq89 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq89 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq109 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq93 (σ X0) (σ X1)
       grind)
    | exact superpose eq93 eq13
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq109
    | exact resolve eq109 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq109
  have eq1299 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq116 x y
       grind)
    | exact superpose eq116 eq14
    | (have r₁ := eq14
       have r₂ := eq116 x y
       grind)
    | exact resolve eq14 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq1322 : False := by grind
  exact eq1322

/-- `Equation3364`: `x ◇ y = y ◇ (z ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3364 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3364 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3364.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 (M.op X0 X2))) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (M.op X0 X1)
       have i₂ := eq8 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X1 (M.op X0 X1)) (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    grind
  have eq21 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X1 (M.op X0 X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq8 X0 X0 X1
       grind)
    | exact superpose eq8 eq20
    | exact resolve eq20 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq23 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq27 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23
    | exact resolve eq23 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq31 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq32 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq35 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
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
  clear eq16
  have eq39 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq44 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq47 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X0 X2)) X3) = (M.op X3 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 (M.op X2 (M.op X0 X2)) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X1 (M.op X0 X1))) = (M.op (M.op X2 (M.op X2 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 (M.op X2 (M.op X2 X0)) X3
       have i₂ := eq19 X2 X0 X1
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X1
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (M.op X1 X0) X2
       have i₂ := eq19 X1 X0 X1
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1
    grind
  have eq57 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op X1 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq19 X1 X0 X0
       grind)
    | exact superpose eq19 eq55
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq60 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X2 (M.op X2 X0)) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq48 X0 x X2 X3
       have i₂ := eq8 X0 X3 x
       grind)
    | exact superpose eq8 eq48
    | exact resolve eq48 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq61 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X2 (M.op X0 X2)) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq47 X0 x X2 X3
       have i₂ := eq8 X0 X3 x
       grind)
    | exact superpose eq8 eq47
    | exact resolve eq47 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq62 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq31 (τ X1) X0
       grind)
    | exact superpose eq31 eq17
    | (have j1 := eq31 (τ X1) X0
       grind)
    | exact resolve eq17 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq77 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq167 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq153 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq153
    | exact resolve eq153 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq216 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X0
       have i₂ := eq32 X0 X1 X0
       grind)
    | exact superpose eq32 eq21
    | (have j1 := eq32 X1 X0 x
       grind)
    | exact resolve eq21 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq330 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq34 x y
       grind)
    | exact superpose eq34 eq14
    | (have j1 := eq34 x y
       grind)
    | exact resolve eq14 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq9
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X1
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq167
    | (have j1 := eq34 X1 X0
       grind)
    | exact resolve eq167 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq352 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq352
    | (have j0 := eq352 X0 X1
       grind)
    | exact resolve eq352 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq584 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X0 X1 X2
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq50 X0 X1 (M.op X1 X0)
       have i₂ := eq51 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X2 X1 X0
       have i₂ := eq51 X1 X2 X0
       grind)
    | (have i₁ := eq50 X0 X1 (M.op X0 X1)
       have i₂ := eq51 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq51
  have eq707 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X1))) = (M.op X2 (M.op X3 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X3 (M.op X3 X0)) X1
       have i₂ := eq60 X0 X3 (M.op X1 (M.op X2 X1))
       grind)
    | exact superpose eq60 eq8
    | exact resolve eq8 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X2 (M.op X3 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X3 X0 (M.op X1 (M.op X1 X2))
       have i₂ := eq60 X2 X1 (M.op X3 (M.op X3 X0))
       grind)
    | exact superpose eq60 eq19
    | exact resolve eq19 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq718 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq708 X0 X1 X2 x
       have i₂ := eq19 x X0 X2
       grind)
    | exact superpose eq19 eq708
    | exact resolve eq708 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq719 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq707 X0 X1 X2 x
       have i₂ := eq19 x X0 X2
       grind)
    | exact superpose eq19 eq707
    | exact resolve eq707 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq1324 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 x X0 X1
       have i₂ := eq718 X1 x X0
       grind)
    | exact superpose eq718 eq19
    | exact resolve eq19 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1361 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op X1 (M.op X3 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X1 X0 (M.op X3 (M.op X3 X2))
       have i₂ := eq718 (M.op X0 (M.op X1 X0)) X3 X2
       grind)
    | exact superpose eq718 eq61
    | exact resolve eq61 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq718
  have eq1362 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1361 X0 X1 X2 x
       have i₂ := eq19 x X2 X1
       grind)
    | exact superpose eq19 eq1361
    | exact resolve eq1361 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361
  have eq1549 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77 X1 X0
       have i₂ := eq1324 X1 X0
       grind)
    | (have i₁ := eq77 X1 X0
       have i₂ := eq1324 X0 X1
       grind)
    | exact superpose eq1324 eq77
    | (have j0 := eq77 X1 X0
       grind)
    | exact resolve eq77 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2242 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2310 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq10
    | (have j1 := eq39 X0 X1
       grind)
    | exact resolve eq10 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2345 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2242 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2242
    | (have j0 := eq2242 X0 X1
       grind)
    | exact resolve eq2242 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242
  have eq2637 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2654 : ∀ X0 : G, (k X0 (k (σ (τ X0)) X0)) = X0 ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq74 (τ X0) X0
       grind)
    | exact superpose eq74 eq27
    | (have j1 := eq74 (τ X0) X0
       grind)
    | exact resolve eq27 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq74
  have eq2678 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2654 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2654
    | (have j0 := eq2654 X0
       grind)
    | exact resolve eq2654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2654
  have eq2684 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2637 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2637
    | (have j0 := eq2637 X0 X1
       grind)
    | exact resolve eq2637 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2637
  have eq2685 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2678 X0
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq2678
    | (have j0 := eq2678 X0
       grind)
    | exact resolve eq2678 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq2678
  have eq4367 : ∀ X0 X1 : G, (σ X0) = (k (σ (τ X1)) X1) ∨ (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (τ X0) X0
       have i₂ := eq35 X0 X1
       grind)
    | (have i₁ := eq39 X0 X1
       have i₂ := eq35 X0 (M.op X0 (τ X1))
       grind)
    | exact superpose eq35 eq39
    | (have j1 := eq35 X1 X0
       grind)
    | exact resolve eq39 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq39
  have eq4415 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (σ X0) = (k X1 X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4367 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4367
    | (have j0 := eq4367 X0 X1
       grind)
    | exact resolve eq4367 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4367
  have eq5020 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq330
       have i₂ := eq31 y x
       grind)
    | exact superpose eq31 eq330
    | (have j1 := eq31 y x
       grind)
    | exact resolve eq330 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq5022 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq330
       have i₂ := eq2345 y x
       grind)
    | exact superpose eq2345 eq330
    | (have j1 := eq2345 (σ y) (σ x)
       grind)
    | (have r₁ := eq330
       have r₂ := eq2345 y x
       grind)
    | exact resolve eq330 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq2345
  have eq5023 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq5022
  have eq5025 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq5020
  have eq5034 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq5025
       grind)
    | exact superpose eq5025 eq167
    | exact resolve eq167 eq5025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq5025
  have eq5079 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq5034
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5034
    | exact resolve eq5034 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5034
  have eq5080 : x = (k x y) := by grind
  clear eq5079
  have eq5165 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq5080
       grind)
    | exact superpose eq5080 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq5080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5080
  have eq5186 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq216 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq216
    | (have j0 := eq216 X1 X0
       have j1 := eq12 X1 X0
       grind)
    | exact resolve eq216 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq5343 : ∀ X0 : G, (M.op X0 (M.op y x)) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq719 X0 y x
       have i₂ := eq5165
       grind)
    | exact superpose eq5165 eq719
    | exact resolve eq719 eq5165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5165
  have eq5350 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq5343 X0
       have i₂ := eq603 X0 y x
       grind)
    | (have i₁ := eq5343 X0
       have i₂ := eq603 X0 x y
       grind)
    | exact superpose eq603 eq5343
    | exact resolve eq5343 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5343
  have eq6293 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (τ (σ X0)) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X0 X0
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq342
    | (have j0 := eq342 X1 X0
       have j1 := eq34 X1 X0
       grind)
    | exact resolve eq342 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq6376 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6293 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6293
    | (have j0 := eq6293 X0 X1
       grind)
    | exact resolve eq6293 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6293
  have eq6954 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq342 x x
       have i₂ := eq5023
       grind)
    | exact superpose eq5023 eq342
    | exact resolve eq342 eq5023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5023
  have eq7005 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6954
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6954
    | exact resolve eq6954 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6954
  have eq8025 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (k (σ X0) (σ X0)))) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq44 X0 (k (σ X0) (σ X0))
       have i₂ := eq2685 (σ X0)
       grind)
    | exact superpose eq2685 eq44
    | (have j1 := eq2685 (σ X0)
       grind)
    | exact resolve eq44 eq2685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685
  have eq8028 : ∀ X0 : G, (τ (σ X0)) = (k X0 (k (τ (σ X0)) X0)) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq8025 X0
       have i₂ := eq26 (σ X0) X0
       grind)
    | exact superpose eq26 eq8025
    | (have j0 := eq8025 X0
       grind)
    | exact resolve eq8025 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8025
  have eq8045 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq8028 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq8028
    | (have j0 := eq8028 X0
       grind)
    | exact resolve eq8028 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8028
  have eq8054 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8045 X0
       have i₂ := eq26 (σ X0) X0
       grind)
    | exact superpose eq26 eq8045
    | (have j0 := eq8045 X0
       grind)
    | exact resolve eq8045 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8045
  have eq8062 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8054 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq8054
    | (have j0 := eq8054 X0
       grind)
    | exact resolve eq8054 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8054
  have eq52513 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1324 (σ X1) (σ X0)
       have i₂ := eq368 X1 X0
       grind)
    | exact superpose eq368 eq1324
    | (have j1 := eq368 X1 X0
       grind)
    | exact resolve eq1324 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq74668 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq2310 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310
  have eq74669 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq74668 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq74668
    | (have j0 := eq74668 X0
       grind)
    | exact resolve eq74668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74668
  have eq74851 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq74669 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq74669
    | (have j0 := eq74669 (σ X0)
       grind)
    | exact resolve eq74669 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74669
  have eq74869 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74851 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq74851
    | (have j0 := eq74851 X0
       grind)
    | exact resolve eq74851 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74851
  have eq83830 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq9
    | exact resolve eq9 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7005
  have eq83841 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq83830
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq83830
    | exact resolve eq83830 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83830
  have eq83938 : y = (M.op x x) ∨ x = y ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5186 x x
       have i₂ := eq83841
       grind)
    | exact superpose eq83841 eq5186
    | exact resolve eq5186 eq83841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5186 eq83841
  have eq83948 : y = (M.op x x) ∨ x = y := by grind
  clear eq83938
  have eq83995 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq19 x x X0
       have i₂ := eq83948
       grind)
    | exact superpose eq83948 eq19
    | exact resolve eq19 eq83948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq84004 : (M.op x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq57 x x
       have i₂ := eq83948
       grind)
    | exact superpose eq83948 eq57
    | exact resolve eq57 eq83948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84084 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1362 x x X0
       have i₂ := eq83948
       grind)
    | exact superpose eq83948 eq1362
    | exact resolve eq1362 eq83948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84866 : (M.op x y) = (k (M.op x y) (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq21 x y
       have i₂ := eq83995 y
       grind)
    | exact superpose eq83995 eq21
    | exact resolve eq21 eq83995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq84920 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (k X0 (M.op x y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq77 X0 (M.op x y)
       have i₂ := eq83995 X0
       grind)
    | exact superpose eq83995 eq77
    | (have j0 := eq77 X0 (M.op x y)
       grind)
    | exact resolve eq77 eq83995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq90226 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq52513 y x
       grind)
    | exact superpose eq52513 eq14
    | (have j1 := eq52513 y x
       grind)
    | exact resolve eq14 eq52513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52513
  have eq90418 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90226
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq90226
    | (have j1 := eq12 y x
       grind)
    | exact resolve eq90226 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90422 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq90226
       have i₂ := eq2684 x y
       grind)
    | exact superpose eq2684 eq90226
    | (have j1 := eq2684 x y
       grind)
    | exact resolve eq90226 eq2684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90226
  have eq90424 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k y x) := by grind
  clear eq90422
  have eq90425 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq90424
       have i₂ := eq1324 y x
       grind)
    | (have i₁ := eq90424
       have i₂ := eq1324 x y
       grind)
    | exact superpose eq1324 eq90424
    | exact resolve eq90424 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90424
  have eq90426 : y = (k y x) := by grind
  clear eq90425
  have eq90430 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90418
       have i₂ := eq1324 y x
       grind)
    | (have i₁ := eq90418
       have i₂ := eq1324 x y
       grind)
    | exact superpose eq1324 eq90418
    | exact resolve eq90418 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90418
  have eq90431 : y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq90430
  have eq90432 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq90431
       have i₂ := eq1324 y x
       grind)
    | (have i₁ := eq90431
       have i₂ := eq1324 x y
       grind)
    | exact superpose eq1324 eq90431
    | exact resolve eq90431 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90431
  have eq90687 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq719 X0 y y
       have i₂ := eq90432
       grind)
    | exact superpose eq90432 eq719
    | exact resolve eq719 eq90432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq90715 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op y x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1362 y y X0
       have i₂ := eq90432
       grind)
    | exact superpose eq90432 eq1362
    | exact resolve eq1362 eq90432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90716 : x ≠ y ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1549 y y
       have i₂ := eq90432
       grind)
    | exact superpose eq90432 eq1549
    | (have j0 := eq1549 y y
       grind)
    | (have r₁ := eq1549 x y
       have r₂ := eq90432
       grind)
    | exact resolve eq1549 eq90432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549 eq90432
  have eq90735 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq90715 X0
       have i₂ := eq584 y x X0
       grind)
    | (have i₁ := eq90715 X0
       have i₂ := eq584 x y X0
       grind)
    | exact superpose eq584 eq90715
    | exact resolve eq90715 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq90715
  have eq90740 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq90687 X0
       have i₂ := eq603 X0 y x
       grind)
    | (have i₁ := eq90687 X0
       have i₂ := eq603 X0 x y
       grind)
    | exact superpose eq603 eq90687
    | exact resolve eq90687 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq90687
  have eq90980 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq84084 X0
       have i₂ := eq90735 X0
       grind)
    | exact superpose eq90735 eq84084
    | exact resolve eq84084 eq90735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84084 eq90735
  have eq91483 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op y y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1362 y x X0
       have i₂ := eq90740 y
       grind)
    | exact superpose eq90740 eq1362
    | exact resolve eq1362 eq90740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362 eq90740
  have eq103927 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (k (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4415 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq4415
    | (have j0 := eq4415 X1 (σ X0)
       grind)
    | exact resolve eq4415 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4415
  have eq103936 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (k (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq103927 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq103927
    | (have j0 := eq103927 X0 X1
       grind)
    | exact resolve eq103927 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103927
  have eq103937 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq103936 X0 X1
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq103936
    | (have j0 := eq103936 X0 X1
       grind)
    | exact resolve eq103936 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103936
  have eq103988 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq6376 y x
       grind)
    | exact superpose eq6376 eq14
    | (have j1 := eq6376 y x
       grind)
    | (have r₁ := eq14
       have r₂ := eq6376 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq6376 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq6376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6376
  have eq103997 : (σ y) = (σ (k x x)) ∨ x = y := by
    first
    | (have j1 := eq103937 x y
       grind)
    | (have r₁ := eq103988
       have r₂ := eq103937 x y
       grind)
    | (have r₁ := eq103988
       have r₂ := eq103937 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq103988
       have r₂ := eq103937 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq103988 eq103937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103937 eq103988
  have eq104032 : (k x x) = (τ (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq103997
       grind)
    | exact superpose eq103997 eq9
    | exact resolve eq9 eq103997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103997
  have eq104089 : y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq104032
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq104032
    | exact resolve eq104032 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104032
  have eq104173 : (σ y) = (σ (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq2684 x x
       have i₂ := eq104089
       grind)
    | exact superpose eq104089 eq2684
    | exact resolve eq2684 eq104089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684 eq104089
  have eq104188 : (σ y) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq104173
  have eq104260 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op x x)
       have i₂ := eq104188
       grind)
    | exact superpose eq104188 eq13
    | exact resolve eq13 eq104188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104188
  have eq104310 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op x x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq104260 X0
       have i₂ := eq13 X0 y
       grind)
    | exact superpose eq13 eq104260
    | exact resolve eq104260 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104260
  have eq106706 : (σ (M.op x y)) = (σ (k (M.op x y) y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq104310 (M.op x y)
       have i₂ := eq84866
       grind)
    | exact superpose eq84866 eq104310
    | exact resolve eq104310 eq84866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84866 eq104310
  have eq106734 : (σ (M.op x y)) = (σ (k (M.op x y) y)) ∨ x = y := by grind
  clear eq106706
  have eq110897 : y ≠ (M.op x x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq90980
  have eq110947 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq110897
       have r₂ := eq83948
       grind)
    | exact resolve eq110897 eq83948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83948 eq110897
  have eq111049 : ∀ X0 : G, (M.op X0 y) = (M.op x X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq83995 X0
       have i₂ := eq110947
       grind)
    | exact superpose eq110947 eq83995
    | exact resolve eq83995 eq110947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83995
  have eq111069 : (σ y) = (σ (k y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq106734
       have i₂ := eq110947
       grind)
    | exact superpose eq110947 eq106734
    | exact resolve eq106734 eq110947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106734
  have eq111071 : y ≠ y ∨ y = (k y y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq84920 y
       have i₂ := eq110947
       grind)
    | exact superpose eq110947 eq84920
    | (have r₁ := eq84920 y
       have r₂ := eq110947
       grind)
    | exact resolve eq84920 eq110947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84920 eq110947
  have eq111282 : y ≠ y ∨ y = (k y y) ∨ x = y := by grind
  clear eq111071
  have eq111283 : y = (k y y) ∨ x = y := by grind
  clear eq111282
  have eq111285 : (σ y) = (σ (k y y)) ∨ x = y := by grind
  clear eq111069
  have eq111295 : ∀ X0 : G, (M.op X0 y) = (M.op x X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq111049 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111049
  have eq111519 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq74869 y
       have i₂ := eq111283
       grind)
    | exact superpose eq111283 eq74869
    | (have j0 := eq74869 y
       grind)
    | exact resolve eq74869 eq111283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74869 eq111283
  have eq111535 : (σ y) = (σ (M.op y y)) ∨ x = y := by grind
  clear eq111519
  have eq112102 : ∀ X0 : G, (τ (k X0 (σ y))) = (k (τ X0) (k y y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq26 X0 (k y y)
       have i₂ := eq111285
       grind)
    | exact superpose eq111285 eq26
    | exact resolve eq26 eq111285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111285
  have eq112155 : ∀ X0 : G, (k (τ X0) y) = (k (τ X0) (k y y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq112102 X0
       have i₂ := eq26 X0 y
       grind)
    | exact superpose eq26 eq112102
    | exact resolve eq112102 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq112102
  have eq114330 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq111535
       have i₂ := eq111295 y
       grind)
    | exact superpose eq111295 eq111535
    | exact resolve eq111535 eq111295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114352 : ∀ X0 : G, (τ (k (σ y) X0)) = (k (M.op y y) (τ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq44 (M.op y y) X0
       have i₂ := eq111535
       grind)
    | exact superpose eq111535 eq44
    | exact resolve eq44 eq111535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111535
  have eq114375 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq114330
  have eq114383 : ∀ X0 : G, (k y (τ X0)) = (k (M.op y y) (τ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq114352 X0
       have i₂ := eq44 y X0
       grind)
    | exact superpose eq44 eq114352
    | exact resolve eq114352 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq114352
  have eq143471 : ∀ X0 : G, (k X0 y) = (k X0 (k y y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq112155 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq112155
    | exact resolve eq112155 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112155
  have eq167176 : ∀ X0 : G, (k y X0) = (k (M.op y y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq114383 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq114383
    | exact resolve eq114383 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114383
  have eq167233 : ∀ X0 : G, (k (M.op x y) X0) = (k y X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq167176 X0
       have i₂ := eq111295 y
       grind)
    | exact superpose eq111295 eq167176
    | exact resolve eq167176 eq111295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111295 eq167176
  have eq167326 : ∀ X0 : G, (k (M.op x y) X0) = (k y X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq167233 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167233
  have eq167749 : (k (M.op x y) y) = (k y (k y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq143471 (M.op x y)
       have i₂ := eq167326 (k y y)
       grind)
    | exact superpose eq167326 eq143471
    | exact resolve eq143471 eq167326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143471 eq167326
  have eq167750 : (k (M.op x y) y) = (k y (k y y)) ∨ x = y := by grind
  clear eq167749
  have eq203436 : (M.op x y) = (k y (k y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq84004
       have i₂ := eq167750
       grind)
    | exact superpose eq167750 eq84004
    | exact resolve eq84004 eq167750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84004 eq167750
  have eq203455 : (M.op x y) = (k y (k y y)) ∨ x = y := by grind
  clear eq203436
  have eq203512 : y = (M.op x y) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq8062 y
       have i₂ := eq203455
       grind)
    | exact superpose eq203455 eq8062
    | (have j0 := eq8062 y
       grind)
    | exact resolve eq8062 eq203455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8062 eq203455
  have eq203542 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq203512
       have r₂ := eq90716
       grind)
    | exact resolve eq203512 eq90716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90716 eq203512
  have eq203602 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq203542
       grind)
    | exact superpose eq203542 eq12
    | (have j0 := eq12 y y
       grind)
    | exact resolve eq12 eq203542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203542
  have eq203606 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq203602
  have eq203657 : ∀ X0 : G, (M.op y X0) = (M.op X0 x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq91483 X0
       have i₂ := eq203606
       grind)
    | exact superpose eq203606 eq91483
    | exact resolve eq91483 eq203606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91483
  have eq203910 : ∀ X0 : G, (M.op y X0) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq203657 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203657
  have eq204086 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq203606
       have i₂ := eq203910 y
       grind)
    | exact superpose eq203910 eq203606
    | exact resolve eq203606 eq203910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203606 eq203910
  have eq204161 : y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq204086
  have eq204182 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq204161
       have i₂ := eq1324 y x
       grind)
    | (have i₁ := eq204161
       have i₂ := eq1324 x y
       grind)
    | exact superpose eq1324 eq204161
    | exact resolve eq204161 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204161
  have eq204183 : y = (M.op x y) := by grind
  clear eq204182
  have eq204207 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq5350 X0
       have i₂ := eq204183
       grind)
    | exact superpose eq204183 eq5350
    | exact resolve eq5350 eq204183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5350
  have eq213041 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq204183
       have i₂ := eq204207 x
       grind)
    | exact superpose eq204207 eq204183
    | exact resolve eq204183 eq204207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204207
  have eq213189 : y = (M.op x x) := by grind
  clear eq213041
  have eq213445 : (M.op x y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq57 x x
       have i₂ := eq213189
       grind)
    | exact superpose eq213189 eq57
    | exact resolve eq57 eq213189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq213720 : y = (k y y) := by
    first
    | (have i₁ := eq213445
       have i₂ := eq204183
       grind)
    | exact superpose eq204183 eq213445
    | exact resolve eq213445 eq204183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204183 eq213445
  have eq213826 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq363 y
       have i₂ := eq213720
       grind)
    | exact superpose eq213720 eq363
    | (have j0 := eq363 y
       grind)
    | exact resolve eq363 eq213720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq213720
  have eq213866 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq213826
  have eq219241 : ∀ X0 : G, (τ (σ y)) = X0 ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq342 y X0
       have i₂ := eq213866
       grind)
    | exact superpose eq213866 eq342
    | (have j0 := eq342 y X0
       grind)
    | exact resolve eq342 eq213866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq219395 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq219241 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq219241
    | (have j0 := eq219241 X0
       grind)
    | exact resolve eq219241 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219241
  have eq230691 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq1324 (σ X0) (σ y)
       have i₂ := eq219395 X0
       grind)
    | exact superpose eq219395 eq1324
    | (have j1 := eq219395 X0
       grind)
    | exact resolve eq1324 eq219395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324 eq219395
  have eq230770 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq230691 x
       grind)
    | exact superpose eq230691 eq14
    | (have j1 := eq230691 x
       grind)
    | exact resolve eq14 eq230691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230691
  have eq230794 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq230770
       have i₂ := eq90426
       grind)
    | exact superpose eq90426 eq230770
    | exact resolve eq230770 eq90426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90426 eq230770
  have eq230797 : x = y := by
    first
    | (have r₁ := eq230794
       have r₂ := eq114375
       grind)
    | exact resolve eq230794 eq114375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114375 eq230794
  have eq230798 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq230797
       grind)
    | exact superpose eq230797 eq14
    | exact resolve eq14 eq230797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231009 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq213866
       have i₂ := eq230797
       grind)
    | exact superpose eq230797 eq213866
    | exact resolve eq213866 eq230797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213866
  have eq231073 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq230798
       have i₂ := eq213189
       grind)
    | exact superpose eq213189 eq230798
    | exact resolve eq230798 eq213189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213189 eq230798
  have eq231078 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq231073
       have i₂ := eq231009
       grind)
    | exact superpose eq231009 eq231073
    | exact resolve eq231073 eq231009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231009 eq231073
  have eq231079 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq231078
       have i₂ := eq230797
       grind)
    | exact superpose eq230797 eq231078
    | exact resolve eq231078 eq230797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230797 eq231078
  have eq231080 : False := by grind
  exact eq231080

/-- `Equation3385`: `x ◇ y = z ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation3385 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3385 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3385.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op X1 X3)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 (M.op X1 X3))
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X0 (M.op X1 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq16
  have eq27 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X3 (M.op X2 X0) (M.op X1 X2)
       have i₂ := eq19 X1 X2 X0
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X2 X0) X1 X2
       have i₂ := eq19 X1 X2 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X1 X3) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X3 X0) (M.op X1 X3)
       have i₂ := eq19 X1 X3 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X0 (M.op X1 (M.op X3 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq43 X0 X1 X2 X3
       have i₂ := eq48 X1 (M.op X3 (M.op X2 X0)) X0
       grind)
    | (have i₁ := eq43 X0 X1 X2 X0
       have i₂ := eq48 X0 (M.op X2 X0) (M.op X0 X1)
       grind)
    | exact superpose eq48 eq43
    | exact resolve eq43 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X3 (M.op X2 X0)))) = (M.op X1 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X1 X2 X3
       have i₂ := eq48 X2 X3 X1
       grind)
    | (have i₁ := eq55 X0 X1 X2 (M.op X0 X1)
       have i₂ := eq48 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq48 eq55
    | exact resolve eq55 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq75 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq104 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X0 (M.op X1 X2) X2 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X1 X2 (M.op X2 X0) X3
       have i₂ := eq19 X1 X2 X0
       grind)
    | exact superpose eq19 eq18
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op (M.op X0 (M.op X0 X0)) X1) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq18 X0 X0 X0 X0
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    grind
  have eq113 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op (M.op X0 X1) (M.op X4 (M.op X2 (M.op X3 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X4 (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X2 X3))
       have i₂ := eq18 X2 X3 X0 X1
       grind)
    | exact superpose eq18 eq19
    | exact resolve eq19 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op (M.op X0 (M.op X3 X4)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 (M.op X3 (M.op X4 X1)) (M.op X0 (M.op X3 X4))
       have i₂ := eq18 X3 X4 X0 X1
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op X0 (M.op (M.op X3 X4) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq114 X0 X1 X2 X3 X4
       have i₂ := eq48 (M.op X3 X4) (M.op X2 (M.op X0 X1)) X0
       grind)
    | (have i₁ := eq114 X0 X1 X0 X3 X4
       have i₂ := eq48 X0 (M.op X0 X1) (M.op X0 (M.op X3 X4))
       grind)
    | exact superpose eq48 eq114
    | exact resolve eq114 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op X0 (M.op X1 (M.op X4 (M.op X2 (M.op X3 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq113 X0 X1 X2 X3 X4
       have i₂ := eq48 X1 (M.op X4 (M.op X2 (M.op X3 X1))) X0
       grind)
    | (have i₁ := eq113 X0 X1 X2 X3 X0
       have i₂ := eq48 X0 (M.op X2 (M.op X3 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq48 eq113
    | exact resolve eq113 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq118 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) = (M.op X0 (M.op (M.op X0 X0) X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 X1
       have i₂ := eq48 (M.op X0 X0) X1 X0
       grind)
    | (have i₁ := eq110 X0 (M.op X0 X1)
       have i₂ := eq48 X0 X1 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq48 eq110
    | (have j0 := eq110 X0 X1
       grind)
    | exact resolve eq110 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq122 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op (M.op X2 X3) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq106 X0 x X2 X3
       have i₂ := eq19 X0 x (M.op X2 X3)
       grind)
    | exact superpose eq19 eq106
    | exact resolve eq106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq124 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq104 X0 X1 X2 X3
       have i₂ := eq48 (M.op (M.op X1 X2) X3) (M.op X0 X1) X0
       grind)
    | (have i₁ := eq104 X0 X1 X2 X3
       have i₂ := eq48 X0 X1 (M.op X0 (M.op (M.op X1 X2) X3))
       grind)
    | exact superpose eq48 eq104
    | exact resolve eq104 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq136 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op X0 (M.op X3 (M.op X4 (M.op X2 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq115 X0 X1 X2 X3 X4
       have i₂ := eq48 X4 (M.op X2 (M.op X0 X1)) X3
       grind)
    | (have i₁ := eq115 X0 X1 X0 X3 X4
       have i₂ := eq48 X0 (M.op X0 X1) (M.op X3 X4)
       grind)
    | exact superpose eq48 eq115
    | exact resolve eq115 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq137 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op X0 (M.op X4 (M.op X3 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq116 X0 x X2 X3 X4
       have i₂ := eq57 x X4 X3 X2
       grind)
    | exact superpose eq57 eq116
    | exact resolve eq116 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq116
  have eq139 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) = (M.op X0 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq118 X0 X1
       have i₂ := eq48 X0 X1 X0
       grind)
    | (have i₁ := eq118 X0 (M.op X0 X1)
       have i₂ := eq48 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq48 eq118
    | (have j0 := eq118 X0 X1
       grind)
    | exact resolve eq118 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq143 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X2 X0) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq122 X0 X2 X3
       have i₂ := eq48 X3 X0 X2
       grind)
    | (have i₁ := eq122 (M.op X0 x) X2 X3
       have i₂ := eq48 X0 x (M.op X2 X3)
       grind)
    | exact superpose eq48 eq122
    | exact resolve eq122 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq145 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op (M.op X1 X2) (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq124 X0 X1 X2 X3
       have i₂ := eq48 X3 (M.op X0 X1) (M.op X1 X2)
       grind)
    | (have i₁ := eq124 X0 X1 X2 X3
       have i₂ := eq48 X0 X1 (M.op (M.op X1 X2) X3)
       grind)
    | exact superpose eq48 eq124
    | exact resolve eq124 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq155 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op (M.op X2 X3) X4)) = (M.op X0 (M.op X4 (M.op X3 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq137 X0 X2 X3 X4
       have i₂ := eq48 (M.op X2 X3) X4 X0
       grind)
    | (have i₁ := eq137 X0 X2 X3 (M.op X0 x)
       have i₂ := eq48 X0 x (M.op X0 (M.op X2 X3))
       grind)
    | exact superpose eq48 eq137
    | exact resolve eq137 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq160 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X3 (M.op X2 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq145 X0 x X2 X3
       have i₂ := eq51 X0 x X3 X2
       grind)
    | exact superpose eq51 eq145
    | exact resolve eq145 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq145
  have eq166 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op X3 X2))) = (M.op X0 (M.op X2 (M.op X3 X4))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq155 X0 X4 X3 X2
       have i₂ := eq48 X3 X2 X4
       grind)
    | (have i₁ := eq155 X0 X2 X3 (M.op X0 x)
       have i₂ := eq48 X0 x (M.op X2 X3)
       grind)
    | exact superpose eq48 eq155
    | exact resolve eq155 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq288 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op (M.op X4 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X4 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 X4 (M.op X0 X1) X3 X2
       have i₂ := eq48 X1 X2 X0
       grind)
    | exact superpose eq48 eq18
    | exact resolve eq18 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op (M.op X2 (M.op X3 X4)) (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 X2 X3 (M.op X0 X1) X4
       have i₂ := eq48 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq48 eq18
    | exact resolve eq18 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 X1)
       have i₂ := eq48 X1 (M.op X2 (M.op X3 (M.op X0 X1))) X0
       grind)
    | exact superpose eq48 eq8
    | exact resolve eq8 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X1 (M.op X2 X1))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq297 x X1 X2 X3
       have i₂ := eq136 x X1 X3 X1 X2
       grind)
    | exact superpose eq136 eq297
    | exact resolve eq297 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq301 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X2 (M.op (M.op X3 X4) (M.op X0 (M.op X1 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq294 X0 X1 X2 X3 X4
       have i₂ := eq48 (M.op X3 X4) (M.op X0 (M.op X1 (M.op X2 X3))) X2
       grind)
    | (have i₁ := eq294 X0 X1 X2 X3 X4
       have i₂ := eq48 X0 (M.op X1 (M.op X2 X3)) (M.op X2 (M.op X3 X4))
       grind)
    | exact superpose eq48 eq294
    | exact resolve eq294 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq306 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X4 (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X4 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq288 X0 X1 X2 X3 X4
       have i₂ := eq48 (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X4 (M.op X0 X1))) X4
       grind)
    | (have i₁ := eq288 X0 X1 X2 X0 X4
       have i₂ := eq48 X0 (M.op X4 (M.op X0 X1)) (M.op X4 (M.op X0 (M.op X1 X2)))
       grind)
    | exact superpose eq48 eq288
    | exact resolve eq288 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq320 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 (M.op (M.op X3 X4) (M.op X0 X3))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq301 X0 X1 x X3 X4
       have i₂ := eq136 x X3 X1 (M.op X3 X4) X0
       grind)
    | exact superpose eq136 eq301
    | exact resolve eq301 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq322 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X4 (M.op X0 (M.op (M.op X1 X2) (M.op X3 (M.op X4 (M.op X0 X1)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq306 X0 X1 X2 X3 X4
       have i₂ := eq48 (M.op X1 X2) (M.op X3 (M.op X4 (M.op X0 X1))) X0
       grind)
    | (have i₁ := eq306 X0 X1 X2 X0 X4
       have i₂ := eq48 X0 (M.op X4 (M.op X0 X1)) (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq48 eq306
    | exact resolve eq306 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq332 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 (M.op X3 (M.op X0 (M.op X3 X4)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq320 X0 X1 X3 X4
       have i₂ := eq166 X1 X3 X0 (M.op X3 X4)
       grind)
    | (have i₁ := eq320 X0 X1 X3 X4
       have i₂ := eq166 X1 (M.op X3 X4) X0 X3
       grind)
    | exact superpose eq166 eq320
    | exact resolve eq320 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq333 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq322 X0 X1 X2 X3 x
       have i₂ := eq136 x (M.op X0 X1) X3 X0 (M.op X1 X2)
       grind)
    | exact superpose eq136 eq322
    | exact resolve eq322 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq322
  have eq339 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X4)) = (M.op X1 (M.op X3 (M.op X0 (M.op X3 X4)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq332 X0 X1 X3 X4
       have i₂ := eq48 X1 X4 X0
       grind)
    | (have i₁ := eq332 X0 X1 X3 (M.op X0 X1)
       have i₂ := eq48 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq48 eq332
    | exact resolve eq332 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq340 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq333 X0 X1 X2 X3
       have i₂ := eq166 X0 X1 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq333 X0 X1 X2 X3
       have i₂ := eq166 X0 (M.op X1 X2) X0 X1
       grind)
    | exact superpose eq166 eq333
    | exact resolve eq333 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq343 : ∀ X1 X2 X3 : G, (M.op X3 X2) = (M.op X1 (M.op X3 (M.op X1 X2))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq340 x X1 X2 X3
       have i₂ := eq339 X1 X3 x (M.op X1 X2)
       grind)
    | (have i₁ := eq340 X1 X1 X2 x
       have i₂ := eq339 x X1 X3 (M.op X1 (M.op X1 (M.op X1 X2)))
       grind)
    | exact superpose eq339 eq340
    | exact resolve eq340 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339 eq340
  have eq368 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30 x y
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 x y
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq9
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq30 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq782 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48 X1 X2 X0
       have i₂ := eq143 X1 X0 X2
       grind)
    | exact superpose eq143 eq48
    | exact resolve eq48 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq918 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq160 X2 X1 (M.op X2 X0)
       have i₂ := eq19 X1 X2 X0
       grind)
    | exact superpose eq19 eq160
    | exact resolve eq160 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq919 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X0 X1)) = (M.op X0 (M.op X2 (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq160 (M.op X2 X3) X0 (M.op X2 (M.op X3 X1))
       have i₂ := eq18 X2 X3 X0 X1
       grind)
    | exact superpose eq18 eq160
    | exact resolve eq160 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq928 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq160 x X1 X0
       grind)
    | exact superpose eq160 eq8
    | exact resolve eq8 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X1))) = (M.op X0 (M.op X2 (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq919 X0 X1 X2 X3
       have i₂ := eq48 X3 (M.op X0 X1) X2
       grind)
    | (have i₁ := eq919 X0 X1 X2 X3
       have i₂ := eq48 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq48 eq919
    | exact resolve eq919 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq1087 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X1 X0
       have i₂ := eq928 X1 X0
       grind)
    | (have i₁ := eq75 X1 X0
       have i₂ := eq928 X0 X1
       grind)
    | exact superpose eq928 eq75
    | (have j0 := eq75 X1 X0
       grind)
    | exact resolve eq75 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1192 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1)))) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq111 (M.op X0 X1)
       have i₂ := eq48 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       grind)
    | exact superpose eq48 eq111
    | exact resolve eq111 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq1219 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (k (M.op X0 (M.op X1 (M.op X0 (M.op X1 (M.op X0 X1))))) (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1192 x X0
       have i₂ := eq918 X0 (M.op x X0) x
       grind)
    | (have i₁ := eq1192 X0 X1
       have i₂ := eq918 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq918 eq1192
    | exact resolve eq1192 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918 eq1192
  have eq1232 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 (M.op X1 (M.op X0 X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1219 x X1
       have i₂ := eq298 X1 x (M.op X1 (M.op x X1))
       grind)
    | (have i₁ := eq1219 x X1
       have i₂ := eq298 X1 x x
       grind)
    | exact superpose eq298 eq1219
    | exact resolve eq1219 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1243 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1232 X0 X1
       have i₂ := eq8 X1 X0 X0
       grind)
    | exact superpose eq8 eq1232
    | exact resolve eq1232 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232
  have eq1561 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq298 X1 X0 X0
       have i₂ := eq343 X0 X1 X1
       grind)
    | exact superpose eq343 eq298
    | exact resolve eq298 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq1788 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq1804 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1087 X1 X1
       have i₂ := eq1561 X1 X0
       grind)
    | (have i₁ := eq1087 X1 X1
       have i₂ := eq1561 X0 X1
       grind)
    | exact superpose eq1561 eq1087
    | (have j0 := eq1087 X1 X1
       grind)
    | (have r₁ := eq1087 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq1561 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq1087 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq1561 X0 (M.op X0 X0)
       grind)
    | exact resolve eq1087 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1806 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq160 X2 X1 (M.op X1 X2)
       have i₂ := eq1561 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq160 X2 X1 (M.op X1 X2)
       have i₂ := eq1561 X0 (M.op X1 X2)
       grind)
    | exact superpose eq1561 eq160
    | exact resolve eq160 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq1818 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0
       have i₂ := eq1561 (τ X0) X1
       grind)
    | (have i₁ := eq21 X0
       have i₂ := eq1561 X0 (τ X0)
       grind)
    | exact superpose eq1561 eq21
    | exact resolve eq21 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1957 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X1 (M.op X0 X0)
       have i₂ := eq1788 X0 (σ X1)
       grind)
    | exact superpose eq1788 eq38
    | exact resolve eq38 eq1788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1788
  have eq4762 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 (M.op X2 (M.op X3 (M.op X3 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq166 X1 (M.op X3 X2) X3 X2
       have i₂ := eq1561 (M.op X3 X2) X0
       grind)
    | (have i₁ := eq166 X1 (M.op X3 X2) X3 X2
       have i₂ := eq1561 X0 (M.op X3 X2)
       grind)
    | exact superpose eq1561 eq166
    | exact resolve eq166 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq5056 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X3 X3)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq4762 X3 X1 x X0
       have i₂ := eq8 X0 X0 x
       grind)
    | exact superpose eq8 eq4762
    | exact resolve eq4762 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4762
  have eq8369 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq397 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq397
    | (have j0 := eq397 (τ X0)
       grind)
    | exact resolve eq397 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq8373 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8369 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8369
    | (have j0 := eq8369 X0
       grind)
    | exact resolve eq8369 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8369
  have eq8377 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8373 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8373
    | (have j0 := eq8373 X0
       grind)
    | exact resolve eq8373 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8373
  have eq13906 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq368
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq368
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq368 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq13907 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq13906
  have eq40176 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1957 (σ x) x
       have i₂ := eq13907
       grind)
    | exact superpose eq13907 eq1957
    | exact resolve eq1957 eq13907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13907
  have eq40256 : ∀ X0 : G, y = (k X0 y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq40176 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq40176
    | exact resolve eq40176 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40176
  have eq41761 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8377 y
       have i₂ := eq40256 y
       grind)
    | exact superpose eq40256 eq8377
    | (have j0 := eq8377 y
       grind)
    | (have r₁ := eq8377 y
       have r₂ := eq40256 y
       grind)
    | exact resolve eq8377 eq40256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40256
  have eq41782 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq41761
  have eq43114 : y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1243 y y
       have i₂ := eq41782
       grind)
    | exact superpose eq41782 eq1243
    | exact resolve eq1243 eq41782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243 eq41782
  have eq43130 : y = (k y y) := by
    first
    | (have j1 := eq1804 x y
       grind)
    | (have r₁ := eq43114
       have r₂ := eq1804 x y
       grind)
    | exact resolve eq43114 eq1804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804 eq43114
  have eq44464 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq43130
       grind)
    | exact superpose eq43130 eq12
    | (have j0 := eq12 y y
       grind)
    | exact resolve eq12 eq43130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43130
  have eq44469 : y = (M.op y y) := by grind
  clear eq44464
  have eq46630 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq1561 X0 y
       have i₂ := eq44469
       grind)
    | exact superpose eq44469 eq1561
    | exact resolve eq1561 eq44469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561
  have eq46634 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1806 y X0 X1
       have i₂ := eq44469
       grind)
    | exact superpose eq44469 eq1806
    | exact resolve eq1806 eq44469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1806
  have eq46635 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1818 y x
       have i₂ := eq44469
       grind)
    | exact superpose eq44469 eq1818
    | exact resolve eq1818 eq44469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818
  have eq46637 : ∀ X0 : G, (τ y) = (k X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq1957 y x
       have i₂ := eq44469
       grind)
    | exact superpose eq44469 eq1957
    | exact resolve eq1957 eq44469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq46639 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq5056 X1 X0 y
       have i₂ := eq44469
       grind)
    | exact superpose eq44469 eq5056
    | exact resolve eq5056 eq44469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5056 eq44469
  have eq51633 : (σ (σ y)) ≠ (σ (σ y)) ∨ (σ (σ y)) = (M.op (σ (σ y)) (σ (σ y))) := by
    first
    | (have i₁ := eq397 (σ y)
       have i₂ := eq46635 (σ y)
       grind)
    | exact superpose eq46635 eq397
    | (have j0 := eq397 (σ y)
       grind)
    | exact resolve eq397 eq46635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq46635
  have eq51660 : (σ (σ y)) = (M.op (σ (σ y)) (σ (σ y))) := by grind
  clear eq51633
  have eq51675 : y = (σ (σ y)) := by
    first
    | (have i₁ := eq51660
       have i₂ := eq46630 (σ (σ y))
       grind)
    | exact superpose eq46630 eq51660
    | exact resolve eq51660 eq46630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51660
  have eq54444 : (σ y) = (τ y) := by
    first
    | (have i₁ := eq9 (σ y)
       have i₂ := eq51675
       grind)
    | exact superpose eq51675 eq9
    | exact resolve eq9 eq51675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51675
  have eq55303 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) := by
    first
    | (have i₁ := eq8377 (τ y)
       have i₂ := eq46637 (τ y)
       grind)
    | exact superpose eq46637 eq8377
    | (have j0 := eq8377 (τ y)
       grind)
    | (have r₁ := eq8377 (τ y)
       have r₂ := eq46637 (τ y)
       grind)
    | exact resolve eq8377 eq46637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8377 eq46637
  have eq55331 : (τ y) = (M.op (τ y) (τ y)) := by grind
  clear eq55303
  have eq55355 : y = (τ y) := by
    first
    | (have i₁ := eq55331
       have i₂ := eq46630 (τ y)
       grind)
    | exact superpose eq46630 eq55331
    | exact resolve eq55331 eq46630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55331
  have eq56638 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq55355
       grind)
    | exact superpose eq55355 eq10
    | exact resolve eq10 eq55355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55355
  have eq57604 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq56638
       grind)
    | exact superpose eq56638 eq14
    | exact resolve eq14 eq56638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57629 : ∀ X0 : G, (τ (M.op y y)) = X0 ∨ (M.op y (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq379 y x
       have i₂ := eq56638
       grind)
    | exact superpose eq56638 eq379
    | exact resolve eq379 eq56638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq57630 : ∀ X0 : G, (τ y) = X0 ∨ (M.op y (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq57629 X0
       have i₂ := eq46630 y
       grind)
    | exact superpose eq46630 eq57629
    | (have j0 := eq57629 X0
       grind)
    | exact resolve eq57629 eq46630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57629
  have eq57643 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq57604
       have i₂ := eq928 (σ x) y
       grind)
    | (have i₁ := eq57604
       have i₂ := eq928 y (σ x)
       grind)
    | exact superpose eq928 eq57604
    | exact resolve eq57604 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57604
  have eq57644 : ∀ X0 : G, (σ y) = X0 ∨ (M.op y (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq57630 X0
       have i₂ := eq54444
       grind)
    | exact superpose eq54444 eq57630
    | (have j0 := eq57630 X0
       grind)
    | exact resolve eq57630 eq54444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54444 eq57630
  have eq57656 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq57644 X0
       have i₂ := eq56638
       grind)
    | exact superpose eq56638 eq57644
    | (have j0 := eq57644 X0
       grind)
    | exact resolve eq57644 eq56638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57644
  have eq69150 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1))) = (k (M.op (M.op X0 X0) (M.op (M.op X0 X0) y)) X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq139 (M.op X1 X1) X1
       have i₂ := eq46639 (M.op X1 X1) X1
       grind)
    | exact superpose eq46639 eq139
    | exact resolve eq139 eq46639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq69406 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1))) = (k (M.op (M.op X0 X0) (M.op y (M.op X0 X0))) X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69150 X0 X1
       have i₂ := eq782 (M.op X0 X0) (M.op X0 X0) y
       grind)
    | (have i₁ := eq69150 X0 X1
       have i₂ := eq782 (M.op X0 X0) y (M.op X0 X0)
       grind)
    | exact superpose eq782 eq69150
    | (have j0 := eq69150 X0 X1
       grind)
    | exact resolve eq69150 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782 eq69150
  have eq69675 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1))) = (k (M.op X0 (M.op (M.op X0 X0) (M.op y X0))) X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69406 X0 X1
       have i₂ := eq967 X0 X0 (M.op X0 X0) y
       grind)
    | (have i₁ := eq69406 X1 X1
       have i₂ := eq967 (M.op X1 X1) X1 y X1
       grind)
    | exact superpose eq967 eq69406
    | (have j0 := eq69406 X0 X1
       grind)
    | exact resolve eq69406 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967 eq69406
  have eq69808 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1))) = (k (M.op (M.op X0 X0) y) X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69675 X0 X1
       have i₂ := eq8 (M.op X0 X0) y X0
       grind)
    | exact superpose eq8 eq69675
    | (have j0 := eq69675 X0 X1
       grind)
    | exact resolve eq69675 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69675
  have eq69850 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1))) = (k (M.op y (M.op X0 X0)) X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69808 X0 X1
       have i₂ := eq928 (M.op X0 X0) y
       grind)
    | (have i₁ := eq69808 X0 X1
       have i₂ := eq928 y (M.op X0 X0)
       grind)
    | exact superpose eq928 eq69808
    | (have j0 := eq69808 X0 X1
       grind)
    | exact resolve eq69808 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69808
  have eq69867 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1))) = (k (M.op y y) X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69850 X0 X1
       have i₂ := eq46639 y X0
       grind)
    | exact superpose eq46639 eq69850
    | (have j0 := eq69850 X0 X1
       grind)
    | exact resolve eq69850 eq46639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69850
  have eq69878 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1))) = (k y X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69867 X0 X1
       have i₂ := eq46630 y
       grind)
    | exact superpose eq46630 eq69867
    | (have j0 := eq69867 X0 X1
       grind)
    | exact resolve eq69867 eq46630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69867
  have eq69883 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k y X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69878 X0 X1
       have i₂ := eq343 (M.op X0 X0) X1 (M.op X0 X0)
       grind)
    | exact superpose eq343 eq69878
    | (have j0 := eq69878 X0 X1
       grind)
    | exact resolve eq69878 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq69878
  have eq69884 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k y X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69883 X0 X1
       have i₂ := eq48 X0 X1 X0
       grind)
    | (have i₁ := eq69883 X0 (M.op X0 X1)
       have i₂ := eq48 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq48 eq69883
    | (have j0 := eq69883 X0 X1
       grind)
    | exact resolve eq69883 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq69883
  have eq69885 : ∀ X0 X1 : G, (M.op X1 y) = (k y X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69884 X0 X1
       have i₂ := eq46634 X0 X1
       grind)
    | exact superpose eq46634 eq69884
    | (have j0 := eq69884 X0 X1
       grind)
    | exact resolve eq69884 eq46634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46634 eq69884
  have eq69886 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = X1 ∨ (M.op X1 y) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69885 X0 X1
       have i₂ := eq928 (M.op X0 X0) y
       grind)
    | (have i₁ := eq69885 X0 X1
       have i₂ := eq928 y (M.op X0 X0)
       grind)
    | exact superpose eq928 eq69885
    | (have j0 := eq69885 X0 X1
       grind)
    | exact resolve eq69885 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928 eq69885
  have eq69887 : ∀ X1 : G, (M.op y y) = X1 ∨ (M.op X1 y) = (k y X1) := by
    intro X1
    first
    | (have i₁ := eq69886 x X1
       have i₂ := eq46639 y x
       grind)
    | exact superpose eq46639 eq69886
    | (have j0 := eq69886 x X1
       grind)
    | exact resolve eq69886 eq46639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46639 eq69886
  have eq69888 : ∀ X1 : G, (M.op X1 y) = (k y X1) ∨ y = X1 := by
    intro X1
    first
    | (have i₁ := eq69887 X1
       have i₂ := eq46630 y
       grind)
    | exact superpose eq46630 eq69887
    | (have j0 := eq69887 X1
       grind)
    | exact resolve eq69887 eq46630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69887
  have eq204728 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op X0 y)) ∨ y = X0 ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq57656 X0
       have i₂ := eq69888 X0
       grind)
    | exact superpose eq69888 eq57656
    | (have j0 := eq57656 X0
       have j1 := eq69888 X0
       grind)
    | exact resolve eq57656 eq69888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57656 eq69888
  have eq204804 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op X0 y)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq204728 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204728
  have eq218226 : (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq57643
       have i₂ := eq204804 x
       grind)
    | exact superpose eq204804 eq57643
    | (have j1 := eq204804 x
       grind)
    | (have r₁ := eq57643
       have r₂ := eq204804 x
       grind)
    | exact resolve eq57643 eq204804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57643 eq204804
  have eq218245 : x = y := by grind
  clear eq218226
  have eq218371 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq218245
       grind)
    | exact superpose eq218245 eq14
    | exact resolve eq14 eq218245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218245
  have eq218549 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq218371
       have i₂ := eq46630 x
       grind)
    | exact superpose eq46630 eq218371
    | exact resolve eq218371 eq46630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218371
  have eq218571 : y ≠ (σ y) := by
    first
    | (have i₁ := eq218549
       have i₂ := eq46630 (σ x)
       grind)
    | exact superpose eq46630 eq218549
    | exact resolve eq218549 eq46630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46630 eq218549
  have eq218585 : False := by grind
  exact eq218585

/-- `Equation3417`: `x ◇ y = z ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3417 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3417 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3417.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X1 X0))) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X1 X0)) X2) = (M.op X3 (M.op X3 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 (M.op X1 X0)) X2 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 X0) X2 X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1 X2 x
       have i₂ := eq8 X1 X0 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X1 X2
       have i₂ := eq19 (M.op X1 X0) X2 X2
       grind)
    | (have i₁ := eq20 X0 X1 (M.op X0 X1)
       have i₂ := eq19 X0 X1 (M.op (M.op X0 X1) (M.op X1 X0))
       grind)
    | exact superpose eq19 eq20
    | exact resolve eq20 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq23 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq27 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23
    | exact resolve eq23 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq30 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq36 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X1 X0) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 X0 (M.op X2 X3)
       have i₂ := eq19 X3 X2 (M.op X1 X0)
       grind)
    | (have i₁ := eq19 X0 X1 X2
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op X1 X0)
       have i₂ := eq21 X0 X1 (M.op X1 X0)
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq119 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X0 X2
       have i₂ := eq90 X2 (M.op X0 X1)
       grind)
    | (have i₁ := eq8 X1 X0 X2
       have i₂ := eq90 (M.op X0 X1) X2
       grind)
    | exact superpose eq90 eq8
    | exact resolve eq8 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
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
  have eq128 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq132 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq27 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq27
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq27 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq178 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq41
  have eq193 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq178
    | exact resolve eq178 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq226 : ∀ X0 X1 X2 : G, (M.op X2 X1) ≠ (M.op X0 (M.op X1 X2)) ∨ (M.op X2 X1) = (k (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq128 (M.op X2 X1) X0
       have i₂ := eq19 X1 X2 X0
       grind)
    | (have i₁ := eq128 X2 (M.op X0 X1)
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq128
    | (have j0 := eq128 (M.op X2 X1) X0
       grind)
    | exact resolve eq128 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq235 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq33
    | (have j0 := eq33 X1 X0
       have j1 := eq33 X1 X0
       grind)
    | exact resolve eq33 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq33 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq33
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33 x y
       grind)
    | exact superpose eq33 eq14
    | (have j1 := eq33 x y
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X1) (σ X0)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq90
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq90 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq339 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq193 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq193 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq193
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq193 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1779 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    grind
  clear eq55
  have eq2800 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq278 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq278
    | (have j0 := eq278 (τ X0)
       grind)
    | exact resolve eq278 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq2802 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2800 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2800
    | (have j0 := eq2800 X0
       grind)
    | exact resolve eq2800 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2800
  have eq2805 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2802 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2802
    | (have j0 := eq2802 X0
       grind)
    | exact resolve eq2802 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2802
  have eq2818 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2805 (τ X0)
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq2805
    | (have j0 := eq2805 (τ X0)
       grind)
    | exact resolve eq2805 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq2805
  have eq2829 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 X0
       have i₂ := eq90 X1 (τ X0)
       grind)
    | (have i₁ := eq36 X1 X0
       have i₂ := eq90 (τ X0) X1
       grind)
    | exact superpose eq90 eq36
    | (have j0 := eq36 X1 X0
       grind)
    | exact resolve eq36 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2852 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq2974 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2852 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2852
    | (have j0 := eq2852 X0 X1
       grind)
    | exact resolve eq2852 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852
  have eq3489 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq122 X0 X0
       grind)
    | exact superpose eq122 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq122 X0 X0
       grind)
    | exact resolve eq12 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq4021 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq250
       have i₂ := eq2974 y x
       grind)
    | exact superpose eq2974 eq250
    | (have j1 := eq2974 (σ y) (σ x)
       grind)
    | (have r₁ := eq250
       have r₂ := eq2974 y x
       grind)
    | exact resolve eq250 eq2974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4022 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq4021
  have eq4035 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq193 x
       have i₂ := eq4022
       grind)
    | exact superpose eq4022 eq193
    | exact resolve eq193 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4080 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4035
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4035
    | exact resolve eq4035 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4035
  have eq4160 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq4080
       grind)
    | exact superpose eq4080 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq4080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4164 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2974 y x
       have i₂ := eq4080
       grind)
    | exact superpose eq4080 eq2974
    | (have j0 := eq2974 y x
       grind)
    | exact resolve eq2974 eq4080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2974 eq4080
  have eq4165 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq4164
  have eq4166 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq4160
  have eq5675 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq261 x x
       have i₂ := eq4022
       grind)
    | exact superpose eq4022 eq261
    | exact resolve eq261 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq5753 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5675
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5675
    | exact resolve eq5675 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5675
  have eq9781 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X1) (σ X0)
       have i₂ := eq235 X1 X0
       grind)
    | exact superpose eq235 eq90
    | (have j1 := eq235 X1 X0
       grind)
    | exact resolve eq90 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq17283 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq278 (τ X0)
       have i₂ := eq132 (τ X0) X0
       grind)
    | exact superpose eq132 eq278
    | (have j0 := eq278 (τ X0)
       have j1 := eq132 (τ X0) X0
       grind)
    | exact resolve eq278 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq17338 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq17283 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17283
    | (have j0 := eq17283 X0
       grind)
    | exact resolve eq17283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17283
  have eq17370 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq17338 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17338
    | (have j0 := eq17338 X0
       grind)
    | exact resolve eq17338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17338
  have eq17392 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq17370 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17370
    | (have j0 := eq17370 X0
       grind)
    | exact resolve eq17370 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17370
  have eq17408 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq17392 X0
       have j1 := eq128 X0 X0
       grind)
    | (have r₁ := eq17392 x
       have r₂ := eq128 x x
       grind)
    | exact resolve eq17392 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17392
  have eq18122 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq17408 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq17408
    | (have j0 := eq17408 (σ X0)
       grind)
    | exact resolve eq17408 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17408
  have eq18160 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18122 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq18122
    | (have j0 := eq18122 X0
       grind)
    | exact resolve eq18122 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18122
  have eq28513 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2829 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2829
    | exact resolve eq2829 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2829
  have eq28950 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28513 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq28513
    | (have j0 := eq28513 X0 X1
       grind)
    | exact resolve eq28513 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28513
  have eq29196 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X0)
       have i₂ := eq28950 X0 X1
       grind)
    | exact superpose eq28950 eq9
    | (have j1 := eq28950 X0 X1
       grind)
    | exact resolve eq9 eq28950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29305 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  clear eq28950
  have eq29514 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29196 X0 X1
       have i₂ := eq9 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq29196
    | (have j0 := eq29196 X0 X1
       grind)
    | exact resolve eq29196 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29196
  have eq30278 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq43920 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq193 X1
       have i₂ := eq259 X1 X0
       grind)
    | exact superpose eq259 eq193
    | (have j1 := eq259 X1 X0
       grind)
    | exact resolve eq193 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq259
  have eq44065 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43920 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq43920
    | (have j0 := eq43920 X0 X1
       grind)
    | exact resolve eq43920 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43920
  have eq66593 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2818 (σ X0)
       have i₂ := eq339 (σ X0) X0
       grind)
    | exact superpose eq339 eq2818
    | (have j0 := eq2818 (σ X0)
       have j1 := eq339 (σ X0) X0
       grind)
    | exact resolve eq2818 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339 eq2818
  have eq66627 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq66593 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq66593
    | (have j0 := eq66593 X0
       grind)
    | exact resolve eq66593 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66593
  have eq66641 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq66627 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq66627
    | (have j0 := eq66627 X0
       grind)
    | exact resolve eq66627 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66627
  have eq66647 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq66641 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq66641
    | (have j0 := eq66641 X0
       grind)
    | exact resolve eq66641 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66641
  have eq66651 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq66647 X0
       have j1 := eq128 X0 X0
       grind)
    | (have r₁ := eq66647 x
       have r₂ := eq128 x x
       grind)
    | exact resolve eq66647 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq66647
  have eq67275 : x ≠ (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66651 x
       have i₂ := eq4022
       grind)
    | exact superpose eq4022 eq66651
    | (have j0 := eq66651 x
       grind)
    | exact resolve eq66651 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66651
  have eq67316 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq67275
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq67275
    | exact resolve eq67275 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67275
  have eq91529 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44065 x y
       grind)
    | exact superpose eq44065 eq14
    | (have j1 := eq44065 x y
       grind)
    | exact resolve eq14 eq44065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44065
  have eq91813 : y = (k y x) := by
    first
    | (have j1 := eq29305 x y
       grind)
    | (have r₁ := eq91529
       have r₂ := eq29305 x y
       grind)
    | exact resolve eq91529 eq29305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29305 eq91529
  have eq93746 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29514 x y
       have i₂ := eq91813
       grind)
    | exact superpose eq91813 eq29514
    | (have j0 := eq29514 x y
       grind)
    | exact resolve eq29514 eq91813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29514
  have eq107157 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq5753
       grind)
    | exact superpose eq5753 eq9
    | exact resolve eq9 eq5753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5753
  have eq107167 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq107157
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq107157
    | exact resolve eq107157 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107157
  have eq107225 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq30278 x x
       have i₂ := eq107167
       grind)
    | exact superpose eq107167 eq30278
    | exact resolve eq30278 eq107167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30278 eq107167
  have eq107228 : y = (M.op x x) ∨ x = y := by grind
  clear eq107225
  have eq107309 : ∀ X0 : G, y = (M.op X0 (M.op y X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq119 x x x
       have i₂ := eq107228
       grind)
    | exact superpose eq107228 eq119
    | exact resolve eq119 eq107228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107228
  have eq107472 : y = (M.op y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq107309 y
       have i₂ := eq93746
       grind)
    | exact superpose eq93746 eq107309
    | exact resolve eq107309 eq93746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107596 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ (M.op X0 y) = (k (M.op X0 y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq226 X0 y X0
       have i₂ := eq107309 X0
       grind)
    | exact superpose eq107309 eq226
    | (have j0 := eq226 X0 y X0
       grind)
    | exact resolve eq226 eq107309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq107309
  have eq108123 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq107472
       have i₂ := eq90 y x
       grind)
    | (have i₁ := eq107472
       have i₂ := eq90 x y
       grind)
    | exact superpose eq90 eq107472
    | exact resolve eq107472 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107472
  have eq108124 : y = (M.op x y) ∨ x = y := by grind
  clear eq108123
  have eq108340 : (M.op y x) = (k (M.op y x) (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq1779 x y
       have i₂ := eq108124
       grind)
    | exact superpose eq108124 eq1779
    | exact resolve eq1779 eq108124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779 eq108124
  have eq108385 : (M.op x y) = (k (M.op x y) (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq108340
       have i₂ := eq90 y x
       grind)
    | (have i₁ := eq108340
       have i₂ := eq90 x y
       grind)
    | exact superpose eq90 eq108340
    | exact resolve eq108340 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108340
  have eq131769 : (M.op x y) = (k (M.op x y) x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq108385
       have i₂ := eq93746
       grind)
    | exact superpose eq93746 eq108385
    | exact resolve eq108385 eq93746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108385
  have eq131771 : (M.op x y) = (k (M.op x y) x) ∨ x = y := by
    first
    | (have j1 := eq107596 x
       grind)
    | (have r₁ := eq131769
       have r₂ := eq107596 x
       grind)
    | exact resolve eq131769 eq107596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107596 eq131769
  have eq131837 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq131771
       have i₂ := eq4166
       grind)
    | exact superpose eq4166 eq131771
    | exact resolve eq131771 eq4166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4166 eq131771
  have eq131865 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq131837
       have r₂ := eq67316
       grind)
    | exact resolve eq131837 eq67316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67316 eq131837
  have eq131993 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq278 x
       have i₂ := eq131865
       grind)
    | exact superpose eq131865 eq278
    | (have j0 := eq278 x
       grind)
    | exact resolve eq278 eq131865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq131865
  have eq132032 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq131993
  have eq134685 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq119 (σ x) (σ x) x
       have i₂ := eq132032
       grind)
    | exact superpose eq132032 eq119
    | exact resolve eq119 eq132032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132032
  have eq135568 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq134685 (σ x)
       have i₂ := eq4022
       grind)
    | exact superpose eq4022 eq134685
    | exact resolve eq134685 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4022 eq134685
  have eq135784 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq135568
  have eq135866 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq135784
       grind)
    | exact superpose eq135784 eq14
    | exact resolve eq14 eq135784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135784
  have eq135976 : y = (M.op x x) := by
    first
    | (have r₁ := eq135866
       have r₂ := eq4165
       grind)
    | exact resolve eq135866 eq4165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4165 eq135866
  have eq136002 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq18160 x
       have i₂ := eq135976
       grind)
    | exact superpose eq135976 eq18160
    | (have j0 := eq18160 x
       grind)
    | exact resolve eq18160 eq135976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18160
  have eq136043 : ∀ X0 : G, y = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq119 x x x
       have i₂ := eq135976
       grind)
    | exact superpose eq135976 eq119
    | exact resolve eq119 eq135976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136225 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq136043 y
       have i₂ := eq93746
       grind)
    | exact superpose eq93746 eq136043
    | exact resolve eq136043 eq93746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93746 eq136043
  have eq137181 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq136225
       have i₂ := eq90 y x
       grind)
    | (have i₁ := eq136225
       have i₂ := eq90 x y
       grind)
    | exact superpose eq90 eq136225
    | exact resolve eq136225 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq136225
  have eq137182 : y = (M.op x y) := by grind
  clear eq137181
  have eq148561 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq3489 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3489
  have eq148562 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq148561 X0 X1
       have j1 := eq236 X1 X0
       grind)
    | (have r₁ := eq148561 (k X1 X1) X0
       have r₂ := eq236 X0 X1
       grind)
    | (have r₁ := eq148561 X0 (σ (k X1 X1))
       have r₂ := eq236 (σ X0) X1
       grind)
    | (have r₁ := eq148561 X1 X0
       have r₂ := eq236 X0 X1
       grind)
    | exact resolve eq148561 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq148561
  have eq148592 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq148562 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq148562 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq148562 eq16
    | (have j1 := eq148562 (τ X1) X0
       grind)
    | exact resolve eq16 eq148562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148562
  have eq148613 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq148592 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq148592
    | (have j0 := eq148592 X0 X1
       grind)
    | exact resolve eq148592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148592
  have eq148619 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq148613 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq148613
    | (have j0 := eq148613 X0 X1
       grind)
    | exact resolve eq148613 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148613
  have eq148820 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ (τ X1))) ∨ (M.op (τ X1) X0) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq148619 X0 (τ X1)
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq148619 (k (τ X0) X1) X1
       grind)
    | exact superpose eq148619 eq16
    | (have j1 := eq148619 X0 (τ X1)
       grind)
    | exact resolve eq16 eq148619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq148619
  have eq148851 : ∀ X0 X1 : G, (σ X0) = (k X1 X1) ∨ (M.op (τ X1) X0) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq148820 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq148820
    | (have j0 := eq148820 X0 X1
       grind)
    | exact resolve eq148820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148820
  have eq151641 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (k (τ (σ X1)) X0) = (M.op (τ (σ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq148851 X0 (σ X1)
       grind)
    | exact superpose eq148851 eq13
    | (have j1 := eq148851 X0 (σ X1)
       grind)
    | exact resolve eq13 eq148851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148851
  have eq151659 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq151641 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq151641
    | (have j0 := eq151641 X0 X1
       grind)
    | exact resolve eq151641 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151641
  have eq151884 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq9781 y x
       grind)
    | exact superpose eq9781 eq14
    | (have j1 := eq9781 y x
       grind)
    | exact resolve eq14 eq9781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9781
  have eq151886 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq151884
       have i₂ := eq91813
       grind)
    | exact superpose eq91813 eq151884
    | exact resolve eq151884 eq91813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91813 eq151884
  have eq151888 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq151886
       have i₂ := eq137182
       grind)
    | exact superpose eq137182 eq151886
    | exact resolve eq151886 eq137182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151886
  have eq151889 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq151888
  have eq151921 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq151889
       grind)
    | exact superpose eq151889 eq9
    | exact resolve eq9 eq151889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151889
  have eq151937 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq151921
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq151921
    | exact resolve eq151921 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151921
  have eq152016 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq151659 y y
       have i₂ := eq151937
       grind)
    | exact superpose eq151937 eq151659
    | exact resolve eq151659 eq151937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151659 eq151937
  have eq152017 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq152016
  have eq152125 : ∀ X0 : G, x = (M.op X0 (M.op x X0)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq119 y y x
       have i₂ := eq152017
       grind)
    | exact superpose eq152017 eq119
    | exact resolve eq119 eq152017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq152017
  have eq152321 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq152125 x
       have i₂ := eq135976
       grind)
    | exact superpose eq135976 eq152125
    | exact resolve eq152125 eq135976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152125
  have eq152929 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq152321
       have i₂ := eq137182
       grind)
    | exact superpose eq137182 eq152321
    | exact resolve eq152321 eq137182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137182 eq152321
  have eq153009 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq152929
       grind)
    | exact superpose eq152929 eq9
    | exact resolve eq9 eq152929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152929
  have eq153085 : x = y ∨ x = y := by
    first
    | (have i₁ := eq153009
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq153009
    | exact resolve eq153009 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153009
  have eq153086 : x = y := by grind
  clear eq153085
  have eq153092 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq153086
       grind)
    | exact superpose eq153086 eq14
    | exact resolve eq14 eq153086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153093 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq250
       have i₂ := eq153086
       grind)
    | exact superpose eq153086 eq250
    | exact resolve eq250 eq153086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq153160 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq136002
       have i₂ := eq153086
       grind)
    | exact superpose eq153086 eq136002
    | exact resolve eq136002 eq153086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136002
  have eq153180 : (σ x) = (σ (k x x)) := by grind
  clear eq153160
  have eq153199 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq153093
       have i₂ := eq135976
       grind)
    | exact superpose eq135976 eq153093
    | exact resolve eq153093 eq135976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153093
  have eq153200 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq153092
       have i₂ := eq135976
       grind)
    | exact superpose eq135976 eq153092
    | exact resolve eq153092 eq135976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135976 eq153092
  have eq153206 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq153199
       have i₂ := eq153180
       grind)
    | exact superpose eq153180 eq153199
    | exact resolve eq153199 eq153180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153180 eq153199
  have eq153207 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq153200
       have i₂ := eq153086
       grind)
    | exact superpose eq153086 eq153200
    | exact resolve eq153200 eq153086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153200
  have eq153208 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq153206
       have i₂ := eq153086
       grind)
    | exact superpose eq153086 eq153206
    | exact resolve eq153206 eq153086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153086 eq153206
  have eq153209 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq153208
  have eq153210 : False := by grind
  exact eq153210

/-- `Equation3470`: `x ◇ x = x ◇ ((y ◇ z) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3470 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3470 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3470.models_iff G M).mp hM
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq220 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq226 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq220 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq220 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq220 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq220 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq249 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq226 (σ X0) (σ X1)
       grind)
    | exact superpose eq226 eq13
    | exact resolve eq13 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq249 X0 X1
       have i₂ := eq226 X0 X1
       grind)
    | exact superpose eq226 eq249
    | exact resolve eq249 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq249
  have eq1841 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq260 x y
       grind)
    | exact superpose eq260 eq14
    | (have r₁ := eq14
       have r₂ := eq260 x y
       grind)
    | exact resolve eq14 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq1871 : False := by grind
  exact eq1871

/-- `Equation3487`: `x ◇ x = y ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation3487 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3487 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3487.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (M.op (M.op X2 x) X0)
       have i₂ := eq8 X0 X2 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq20
  have eq45 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq50 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  clear eq15
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq45 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq80 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X0 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X2 X3 (M.op (M.op X2 X2) X3)
       have i₂ := eq23 X1 (M.op (M.op X2 X2) X3) X0
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X2 (M.op (M.op X2 X3) (M.op (M.op X1 X1) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op (M.op X1 X1) X0) X2 X3
       have i₂ := eq23 X1 X0 (M.op (M.op X1 X1) X0)
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X1 X1) X0) X2 x
       have i₂ := eq23 X1 X0 (M.op X2 x)
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq92 X0 x X2
       have i₂ := eq23 x X0 (M.op (M.op x x) X0)
       grind)
    | exact superpose eq23 eq92
    | exact resolve eq92 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq92
  have eq98 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 X1 X2
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq93
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq93 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq93 X0 (M.op X0 X0)
       grind)
    | exact superpose eq93 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq93 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq106 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq151 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq169 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X2 X3) X0)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X2 X3
       have i₂ := eq111 X1 X0
       grind)
    | exact superpose eq111 eq8
    | exact resolve eq8 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) = (M.op X2 (k X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 X1 X2
       have i₂ := eq111 X0 X1
       grind)
    | exact superpose eq111 eq93
    | exact resolve eq93 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq2139 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq151 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq2176 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq2139 (σ X0)
       grind)
    | exact superpose eq2139 eq13
    | exact resolve eq13 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2178 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq2139 (τ X0)
       grind)
    | exact superpose eq2139 eq35
    | exact resolve eq35 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq2181 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2178 X0
       have i₂ := eq2139 X0
       grind)
    | exact superpose eq2139 eq2178
    | exact resolve eq2178 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178
  have eq2183 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2176 X0
       have i₂ := eq2139 X0
       grind)
    | exact superpose eq2139 eq2176
    | exact resolve eq2176 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2139 eq2176
  have eq2637 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (τ X0) x
       have i₂ := eq2181 X0
       grind)
    | exact superpose eq2181 eq93
    | exact resolve eq93 eq2181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2181
  have eq2751 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (σ X0) x
       have i₂ := eq2183 X0
       grind)
    | exact superpose eq2183 eq93
    | exact resolve eq93 eq2183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3501 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq3663 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3501 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq3501
    | (have j0 := eq3501 X0 X1
       grind)
    | exact resolve eq3501 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3501
  have eq6475 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (k X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X2 x (M.op x x) X0
       have i₂ := eq169 X0 X1 (M.op x x) (M.op x x)
       grind)
    | exact superpose eq169 eq80
    | exact resolve eq80 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq169
  have eq8404 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X1 (τ (σ X0))) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2637 (σ X1) X1
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq2637
    | (have j1 := eq49 X2 X0
       grind)
    | exact resolve eq2637 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq2637
  have eq8574 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8404 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq8404
    | (have j0 := eq8404 X0 X1 X2
       grind)
    | exact resolve eq8404 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8404
  have eq9284 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2751 X0 X1
       have i₂ := eq98 X0 X0 X2
       grind)
    | exact superpose eq98 eq2751
    | (have j1 := eq98 (σ X0) X1 X2
       grind)
    | exact resolve eq2751 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq2751
  have eq10923 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X2 X3) (M.op X0 X0))) = (M.op (k X0 (M.op X1 X1)) (k X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq90 (k X0 (M.op X1 X1)) x X2 X3
       have i₂ := eq6475 X0 X1 (M.op x x)
       grind)
    | exact superpose eq6475 eq90
    | exact resolve eq90 eq6475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq6475
  have eq10960 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X1 X1)) = (M.op X2 (M.op (M.op X2 X3) (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10923 X0 X1 X2 X3
       have i₂ := eq175 X0 X1 (k X0 (M.op X1 X1))
       grind)
    | exact superpose eq175 eq10923
    | exact resolve eq10923 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq10923
  have eq11147 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10960 X0 X1 X2 x
       have i₂ := eq93 X0 (M.op X2 x)
       grind)
    | (have i₁ := eq10960 x X1 x x
       have i₂ := eq93 (M.op x x) X2
       grind)
    | exact superpose eq93 eq10960
    | exact resolve eq10960 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10960
  have eq17581 : ∀ X0 X1 X2 : G, (k (σ X0) (M.op X2 X2)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11147 (σ X0) X2 X1
       have i₂ := eq2183 X0
       grind)
    | exact superpose eq2183 eq11147
    | exact resolve eq11147 eq2183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17692 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X0 X0))) = (M.op X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11147 X2 (σ X0) X1
       have i₂ := eq2183 X0
       grind)
    | exact superpose eq2183 eq11147
    | exact resolve eq11147 eq2183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11147
  have eq68233 : ∀ X0 X1 X2 : G, (k (σ X0) (σ (M.op X1 X1))) = (M.op X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17692 X1 X2 (σ X0)
       have i₂ := eq2183 X0
       grind)
    | exact superpose eq2183 eq17692
    | exact resolve eq17692 eq2183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183 eq17692
  have eq68930 : ∀ X0 X1 X2 : G, (σ (k X0 (M.op X1 X1))) = (M.op X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68233 X0 X1 X2
       have i₂ := eq13 X0 (M.op X1 X1)
       grind)
    | exact superpose eq13 eq68233
    | exact resolve eq68233 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68233
  have eq257551 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 X1 X2
       have i₂ := eq3663 X0 X1
       grind)
    | exact superpose eq3663 eq93
    | (have j1 := eq3663 X2 X0
       grind)
    | exact resolve eq93 eq3663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq3663
  have eq297690 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq9284 y (σ x) X0
       grind)
    | exact superpose eq9284 eq14
    | (have j1 := eq9284 y x X0
       grind)
    | exact resolve eq14 eq9284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9284
  have eq438727 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq8574 y X0 x
       grind)
    | exact superpose eq8574 eq14
    | (have j1 := eq8574 y X0 x
       grind)
    | exact resolve eq14 eq8574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8574
  have eq438747 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq438727 X0
       have j1 := eq257551 y X0 x
       grind)
    | (have r₁ := eq438727 X0
       have r₂ := eq257551 y x x
       grind)
    | exact resolve eq438727 eq257551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257551 eq438727
  have eq439111 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (k (σ X0) y) := by
    intro X0 X1
    first
    | (have i₁ := eq17581 X0 X1 y
       have i₂ := eq438747 y
       grind)
    | exact superpose eq438747 eq17581
    | exact resolve eq17581 eq438747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17581
  have eq439239 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (σ (k X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq68930 X0 y X1
       have i₂ := eq438747 y
       grind)
    | exact superpose eq438747 eq68930
    | exact resolve eq68930 eq438747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68930
  have eq439854 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq297690 X0
       have i₂ := eq438747 x
       grind)
    | exact superpose eq438747 eq297690
    | (have j0 := eq297690 X0
       grind)
    | exact resolve eq297690 eq438747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297690
  have eq439855 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq439854 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439854
  have eq439862 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq439855 X0
       have i₂ := eq438747 X0
       grind)
    | exact superpose eq438747 eq439855
    | exact resolve eq439855 eq438747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439855
  have eq440199 : ∀ X0 : G, (k (σ X0) y) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq439111 X0 x
       have i₂ := eq439239 X0 x
       grind)
    | exact superpose eq439239 eq439111
    | exact resolve eq439111 eq439239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439111 eq439239
  have eq440406 : ∀ X0 : G, (σ y) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq440199 X0
       have i₂ := eq439862 X0
       grind)
    | exact superpose eq439862 eq440199
    | exact resolve eq440199 eq439862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440199
  have eq440499 : y = (σ y) := by
    first
    | (have i₁ := eq440406 x
       have i₂ := eq439862 (σ x)
       grind)
    | exact superpose eq439862 eq440406
    | exact resolve eq440406 eq439862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439862 eq440406
  have eq440569 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq440499
       grind)
    | exact superpose eq440499 eq14
    | exact resolve eq14 eq440499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440723 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq440569
       have i₂ := eq438747 (σ x)
       grind)
    | exact superpose eq438747 eq440569
    | exact resolve eq440569 eq438747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440569
  have eq440782 : y ≠ (σ y) := by
    first
    | (have i₁ := eq440723
       have i₂ := eq438747 x
       grind)
    | exact superpose eq438747 eq440723
    | exact resolve eq440723 eq438747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438747 eq440723
  have eq440820 : False := by grind
  exact eq440820
