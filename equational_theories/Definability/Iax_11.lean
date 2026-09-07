import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1724 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq184 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq188 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq184 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq184 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq184 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq207 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq188 (σ X0) (σ X1)
       grind)
    | exact superpose eq188 eq13
    | exact resolve eq13 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq207 X0 X1
       have i₂ := eq188 X0 X1
       grind)
    | exact superpose eq188 eq207
    | exact resolve eq207 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq207
  have eq1478 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq216 x y
       grind)
    | exact superpose eq216 eq14
    | (have r₁ := eq14
       have r₂ := eq216 x y
       grind)
    | exact resolve eq14 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq1511 : False := by grind
  exact eq1511

/-- `Equation1738`: `x = (y ◇ y) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pyx_Equation1738 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1738 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1738.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X0) X0) X1 (M.op (M.op X2 X0) X0)
       have i₂ := eq8 X0 (M.op (M.op X2 X0) X0) X2
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
  have eq27 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 X3) X3)) = X3 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq33 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
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
  have eq41 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq19 (M.op (M.op X2 X0) X0) X3 (M.op x x)
       have i₂ := eq8 X0 x X2
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq19 X1 X3 x
       have i₂ := eq19 X1 X0 x
       grind)
    | (have i₁ := eq19 X0 X1 X0
       have i₂ := eq19 X0 X0 x
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 x
       have i₂ := eq19 X1 X0 x
       grind)
    | (have i₁ := eq8 X0 X1 X0
       have i₂ := eq19 X0 X0 X2
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X0)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq41 X0 X2 x
       have i₂ := eq8 X0 x X2
       grind)
    | exact superpose eq8 eq41
    | exact resolve eq41 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq65 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1 x
       have i₂ := eq19 X1 X0 x
       grind)
    | (have i₁ := eq58 X0 X0
       have i₂ := eq19 X0 X0 x
       grind)
    | exact superpose eq19 eq58
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq58
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
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
  have eq76 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq28 X0 (τ X1)
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 (τ X1)
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq77 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq111 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X2 X3) X3)) = X3 ∨ (M.op (M.op (M.op X1 X0) X0) X4) = (k X4 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X3 (M.op (M.op X1 X0) X0) X2
       have i₂ := eq27 (M.op (M.op X1 X0) X0) X4 X1 X0
       grind)
    | exact superpose eq27 eq8
    | (have j1 := eq27 X0 X1 X2 X3
       grind)
    | exact resolve eq8 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq131 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq175 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq38
  have eq251 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op (M.op X1 X1) X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq77 (M.op (M.op X1 X1) X0) X0
       have i₂ := eq65 X1 X0
       grind)
    | exact superpose eq65 eq77
    | (have j0 := eq77 (M.op (M.op X1 X1) X0) X0
       grind)
    | (have r₁ := eq77 (M.op (M.op X0 X0) X1) X1
       have r₂ := eq65 X0 X1
       grind)
    | exact resolve eq77 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq253 : ∀ X0 X1 : G, (k (M.op (M.op X1 X1) X0) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq251 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq334 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 X2) (M.op (σ (k X0 X1)) (σ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X0) X2 (σ X1)
       have i₂ := eq30 X1 X0
       grind)
    | exact superpose eq30 eq8
    | (have j1 := eq30 X1 X0
       grind)
    | exact resolve eq8 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq30 X1 X0
       grind)
    | exact superpose eq30 eq9
    | (have j1 := eq30 X1 X0
       grind)
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq30 X2 X0
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 X2 X0
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq402 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (M.op X1 X1) (σ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op (M.op X1 X1) (σ X0)) X0
       have i₂ := eq253 (σ X0) X1
       grind)
    | exact superpose eq253 eq24
    | exact resolve eq24 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq253
  have eq405 : ∀ X0 X1 : G, (k (τ (M.op (M.op X1 X1) (σ X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq402
    | exact resolve eq402 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq653 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (M.op X1 X1) X3 X2
       have i₂ := eq46 X1 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq52 (M.op X1 X1) X3 X2
       have i₂ := eq46 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq46 eq52
    | exact resolve eq52 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq52
  have eq1465 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq1563 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1465 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1465
    | (have j0 := eq1465 X0 X1
       grind)
    | exact resolve eq1465 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq2238 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq2294 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2238 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2238
    | (have j0 := eq2238 X0 X1
       grind)
    | exact resolve eq2238 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238
  have eq3406 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X0 X1
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq342
    | (have j0 := eq342 X0 X1
       have j1 := eq72 X0 X1
       grind)
    | exact resolve eq342 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq3486 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3406 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq3406
    | (have j0 := eq3406 X0 X1
       grind)
    | exact resolve eq3406 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406
  have eq4990 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0
       have i₂ := eq342 X0 X1
       grind)
    | (have i₁ := eq175 X0
       have i₂ := eq342 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq342 eq175
    | (have j1 := eq342 X1 X0
       grind)
    | exact resolve eq175 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq342
  have eq10828 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op X2 X2) (M.op (σ (τ (k X0 X1))) (σ (τ X0)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq334 (τ X0) (τ X1) X2
       have i₂ := eq131 X1 X0
       grind)
    | exact superpose eq131 eq334
    | (have j0 := eq334 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq334 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq334
  have eq10975 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (σ (τ (k X0 X1))) X0)) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10828 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10828
    | (have j0 := eq10828 X0 X1 X2
       grind)
    | exact resolve eq10828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10828
  have eq10981 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (k X0 X1) X0)) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10975 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq10975
    | (have j0 := eq10975 X0 X1 X2
       grind)
    | exact resolve eq10975 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10975
  have eq10982 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op (M.op X2 X2) (M.op (k X0 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10981 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10981
    | (have j0 := eq10981 X0 X1 X2
       grind)
    | exact resolve eq10981 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10981
  have eq10983 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (k X0 X1) X0)) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10982 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq10982
    | (have j0 := eq10982 X0 X1 X2
       grind)
    | exact resolve eq10982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10982
  have eq11356 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4990 x y
       grind)
    | exact superpose eq4990 eq14
    | (have j1 := eq4990 x y
       grind)
    | exact resolve eq14 eq4990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4990
  have eq11454 : x = (k y x) := by
    first
    | (have j1 := eq2294 y x
       grind)
    | (have r₁ := eq11356
       have r₂ := eq2294 y x
       grind)
    | exact resolve eq11356 eq2294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2294 eq11356
  have eq11701 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq11454
       grind)
    | exact superpose eq11454 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq11454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11708 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1563 x y
       have i₂ := eq11454
       grind)
    | exact superpose eq11454 eq1563
    | (have j0 := eq1563 x y
       grind)
    | exact resolve eq1563 eq11454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563
  have eq13874 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    grind
  clear eq344
  have eq14876 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X3 X4) X4)) = X4 := by
    intro X0 X1 X2 X3 X4
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f14876_14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
      intro X0 X1 X2
      grind
    have f14876_18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
      intro X0 X1
      grind
    have f14876_21 : (M.op X0 X2) ≠ (k X2 X0) := by grind
    have f14876_22 : X4 ≠ (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X3 X4) X4)) := by grind
    have f14876_32 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X1) X0) := by
      intro X0 X1 X2
      first
      | (have i₁ := f14876_14 (M.op (M.op X2 X0) X0) X1 (M.op (M.op X2 X0) X0)
         have i₂ := f14876_14 X0 (M.op (M.op X2 X0) X0) X2
         grind)
      | exact superpose f14876_14 f14876_14
      | exact resolve f14876_14 f14876_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f14876_49 : (M.op X0 X2) ≠ (M.op X0 X2) ∨ X0 = (M.op X2 X2) := by
      first
      | (have i₁ := f14876_21
         have i₂ := f14876_18 X2 X0
         grind)
      | exact superpose f14876_18 f14876_21
      | (have j1 := f14876_18 X2 X0
         grind)
      | (have r₁ := f14876_21
         have r₂ := f14876_18 X2 X0
         grind)
      | exact resolve f14876_21 f14876_18
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f14876_50 : X0 = (M.op X2 X2) := by grind
    have f14876_78 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 X1) := by
      intro X0 X1
      first
      | (have i₁ := f14876_32 X1 X2 X0
         have i₂ := f14876_50
         grind)
      | exact superpose f14876_50 f14876_32
      | exact resolve f14876_32 f14876_50
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f14876_507 : X4 ≠ (M.op (M.op X0 X0) (M.op (M.op X3 X4) X4)) := by
      first
      | (have i₁ := f14876_22
         have i₂ := f14876_78 X1 X0
         grind)
      | exact superpose f14876_78 f14876_22
      | exact resolve f14876_22 f14876_78
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f14876_520 : False := by
      first
      | (have r₁ := f14876_507
         have r₂ := f14876_14 X4 X0 X3
         grind)
      | exact resolve f14876_507 f14876_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f14876_520
  clear eq111
  have eq92880 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq10983 y x X0
       have i₂ := eq11454
       grind)
    | exact superpose eq11454 eq10983
    | (have j0 := eq10983 y x x
       grind)
    | exact resolve eq10983 eq11454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10983
  have eq96663 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq653 x x X0 (M.op x y)
       have i₂ := eq92880 (M.op x x)
       grind)
    | exact superpose eq92880 eq653
    | exact resolve eq653 eq92880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq92880
  have eq134253 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13874 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13874
  have eq134254 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq134253 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134253
  have eq134302 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq134254 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq134254
    | exact resolve eq134254 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134374 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X0)) (M.op (M.op X1 X2) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (σ X0) X1
       have i₂ := eq134254 X0
       grind)
    | exact superpose eq134254 eq8
    | exact resolve eq8 eq134254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134386 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (k X0 X0)) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (σ X0) X1
       have i₂ := eq134254 X0
       grind)
    | exact superpose eq134254 eq65
    | exact resolve eq65 eq134254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134648 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq134302 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq134302
    | exact resolve eq134302 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq134302
  have eq134662 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq134648 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq134648
    | exact resolve eq134648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134648
  have eq135612 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq134386 X0 X1
       have i₂ := eq134662 X0
       grind)
    | exact superpose eq134662 eq134386
    | exact resolve eq134386 eq134662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134386
  have eq136830 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) X0) = (M.op (M.op X1 X1) (M.op X0 (M.op (σ (M.op X2 X2)) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (σ (M.op X2 X2)) X0) X1 X0
       have i₂ := eq135612 X2 X0
       grind)
    | exact superpose eq135612 eq8
    | exact resolve eq8 eq135612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136897 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (σ (M.op X2 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq136830 X0 X1 X2
       have i₂ := eq135612 X2 X0
       grind)
    | exact superpose eq135612 eq136830
    | exact resolve eq136830 eq135612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135612 eq136830
  have eq138889 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) (M.op (M.op X1 X2) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134374 X0 X1 X2
       have i₂ := eq134662 X0
       grind)
    | exact superpose eq134662 eq134374
    | exact resolve eq134374 eq134662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134374
  have eq155024 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3486 y x
       grind)
    | exact superpose eq3486 eq14
    | (have j1 := eq3486 y x
       grind)
    | exact resolve eq14 eq3486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3486
  have eq155028 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k y y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq155024
       have i₂ := eq11454
       grind)
    | exact superpose eq11454 eq155024
    | exact resolve eq155024 eq11454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11454 eq155024
  have eq155030 : x = (M.op y y) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq155028
       have i₂ := eq134662 y
       grind)
    | exact superpose eq134662 eq155028
    | exact resolve eq155028 eq134662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155028
  have eq155031 : x = (M.op y y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq155030
       have r₂ := eq11708
       grind)
    | exact resolve eq155030 eq11708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11708 eq155030
  have eq155032 : (σ y) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq155031
       have i₂ := eq134662 y
       grind)
    | exact superpose eq134662 eq155031
    | exact resolve eq155031 eq134662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155031
  have eq155062 : (M.op y y) = (τ (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq155032
       grind)
    | exact superpose eq155032 eq9
    | exact resolve eq9 eq155032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155032
  have eq155112 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq155062
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq155062
    | exact resolve eq155062 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155062
  have eq155213 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq96663 y
       have i₂ := eq155112
       grind)
    | exact superpose eq155112 eq96663
    | exact resolve eq96663 eq155112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96663
  have eq155306 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq155112
  have eq155342 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq155213
       have r₂ := eq155306
       grind)
    | exact resolve eq155213 eq155306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155213 eq155306
  have eq156173 : x ≠ (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq155342
  have eq156176 : x = (M.op y y) := by
    first
    | (have r₁ := eq156173
       have r₂ := eq11701
       grind)
    | exact resolve eq156173 eq11701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11701 eq156173
  have eq156283 : ∀ X0 : G, (M.op X0 (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 y X0
       have i₂ := eq156176
       grind)
    | exact superpose eq156176 eq65
    | exact resolve eq65 eq156176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq156299 : ∀ X0 : G, (k (τ (M.op x (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq405 X0 y
       have i₂ := eq156176
       grind)
    | exact superpose eq156176 eq405
    | exact resolve eq405 eq156176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq156434 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq136897 X1 X0 y
       have i₂ := eq156176
       grind)
    | exact superpose eq156176 eq136897
    | exact resolve eq136897 eq156176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136897 eq156176
  have eq156861 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 X1) (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op x X0) X1 X0
       have i₂ := eq156283 X0
       grind)
    | exact superpose eq156283 eq8
    | exact resolve eq8 eq156283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156940 : ∀ X0 X1 : G, (M.op x X0) = (M.op (σ (M.op X1 X1)) (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq138889 X1 X0 (M.op x X0)
       have i₂ := eq156283 X0
       grind)
    | exact superpose eq156283 eq138889
    | exact resolve eq138889 eq156283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138889
  have eq157092 : ∀ X0 X1 : G, (M.op x X0) = (M.op (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq156940 X0 X1
       have i₂ := eq156283 X0
       grind)
    | exact superpose eq156283 eq156940
    | exact resolve eq156940 eq156283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156940
  have eq157133 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) (M.op X0 (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq156861 X0 x
       have i₂ := eq156434 x (M.op X0 (M.op x X0))
       grind)
    | exact superpose eq156434 eq156861
    | exact resolve eq156861 eq156434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156861
  have eq157176 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq157133 X0
       have i₂ := eq156283 X0
       grind)
    | exact superpose eq156283 eq157133
    | exact resolve eq157133 eq156283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156283 eq157133
  have eq159896 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq157176 (σ y)
       grind)
    | exact superpose eq157176 eq14
    | exact resolve eq14 eq157176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179141 : ∀ X0 : G, (σ (k (M.op X0 X0) (M.op X0 X0))) = (M.op x (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq134254 (M.op X0 X0)
       have i₂ := eq157092 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq157092 eq134254
    | exact resolve eq134254 eq157092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134254 eq157092
  have eq179491 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op x (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq179141 X0
       have i₂ := eq134662 (M.op X0 X0)
       grind)
    | exact superpose eq134662 eq179141
    | exact resolve eq179141 eq134662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134662 eq179141
  have eq179633 : ∀ X0 : G, (M.op x (σ (M.op X0 X0))) = (σ (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq179491 X0
       have i₂ := eq156434 X0 (M.op X0 X0)
       grind)
    | exact superpose eq156434 eq179491
    | exact resolve eq179491 eq156434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179491
  have eq179687 : ∀ X0 : G, (σ (M.op x (M.op X0 X0))) = (M.op x (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq179633 X0
       have i₂ := eq157176 (M.op X0 X0)
       grind)
    | exact superpose eq157176 eq179633
    | exact resolve eq179633 eq157176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179633
  have eq294019 : ∀ X0 X2 : G, (M.op x (σ X0)) = (σ (M.op x X0)) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq179687 (M.op (M.op x x) x)
       have i₂ := eq14876 x x X2 x x
       grind)
    | exact superpose eq14876 eq179687
    | (have j1 := eq14876 X0 x X2 x x
       grind)
    | exact resolve eq179687 eq14876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14876 eq179687
  have eq643184 : ∀ X0 : G, (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq159896
       have i₂ := eq294019 y X0
       grind)
    | exact superpose eq294019 eq159896
    | (have j1 := eq294019 y X0
       grind)
    | (have r₁ := eq159896
       have r₂ := eq294019 y x
       grind)
    | exact resolve eq159896 eq294019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294019
  have eq643195 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq643184 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643184
  have eq644135 : y = (M.op y (τ (M.op x (σ y)))) := by
    first
    | (have i₁ := eq156299 y
       have i₂ := eq643195 (τ (M.op x (σ y)))
       grind)
    | exact superpose eq643195 eq156299
    | exact resolve eq156299 eq643195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156299 eq643195
  have eq644967 : ∀ X0 : G, (τ (M.op x (σ y))) = (M.op (M.op X0 X0) (M.op y (τ (M.op x (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq8 (τ (M.op x (σ y))) X0 y
       have i₂ := eq644135
       grind)
    | exact superpose eq644135 eq8
    | exact resolve eq8 eq644135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644988 : (τ (M.op x (σ y))) = (M.op (σ x) (M.op y (τ (M.op x (σ y))))) := by
    first
    | (have i₁ := eq644967 x
       have i₂ := eq156434 x (M.op y (τ (M.op x (σ y))))
       grind)
    | exact superpose eq156434 eq644967
    | exact resolve eq644967 eq156434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156434 eq644967
  have eq645007 : (τ (M.op x (σ y))) = (M.op x (M.op y (τ (M.op x (σ y))))) := by
    first
    | (have i₁ := eq644988
       have i₂ := eq157176 (M.op y (τ (M.op x (σ y))))
       grind)
    | exact superpose eq157176 eq644988
    | exact resolve eq644988 eq157176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157176 eq644988
  have eq645018 : (M.op x y) = (τ (M.op x (σ y))) := by
    first
    | (have i₁ := eq645007
       have i₂ := eq644135
       grind)
    | exact superpose eq644135 eq645007
    | exact resolve eq645007 eq644135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644135 eq645007
  have eq645806 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x (σ y))
       have i₂ := eq645018
       grind)
    | exact superpose eq645018 eq10
    | exact resolve eq10 eq645018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645018
  have eq645836 : False := by grind
  exact eq645836

/-- `Equation1738`: `x = (y ◇ y) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pxx_pyx_Equation1738 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1738 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1738.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  clear eq15
  have eq22 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X0) X0) X1 (M.op (M.op X2 X0) X0)
       have i₂ := eq8 X0 (M.op (M.op X2 X0) X0) X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq41 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq43 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq22 (M.op (M.op X2 X0) X0) X3 (M.op x x)
       have i₂ := eq8 X0 x X2
       grind)
    | exact superpose eq8 eq22
    | exact resolve eq22 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq22 X1 X3 x
       have i₂ := eq22 X1 X0 x
       grind)
    | (have i₁ := eq22 X0 X1 X0
       have i₂ := eq22 X0 X0 x
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X0)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq58 X0 X2 x
       have i₂ := eq8 X0 x X2
       grind)
    | exact superpose eq8 eq58
    | exact resolve eq58 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq82 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X1 x
       have i₂ := eq22 X1 X0 x
       grind)
    | (have i₁ := eq75 X0 X0
       have i₂ := eq22 X0 X0 x
       grind)
    | exact superpose eq22 eq75
    | exact resolve eq75 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq41 X1 X0
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq11 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (M.op X1 X1) (M.op (σ X0) (σ X2))) ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X2) X1 (σ X0)
       have i₂ := eq41 X2 X0
       grind)
    | exact superpose eq41 eq8
    | (have j1 := eq41 X2 X0
       grind)
    | exact resolve eq8 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq172 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq171 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq171
    | (have j0 := eq171 X0 X1
       grind)
    | exact resolve eq171 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq246 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X3 (M.op X1 X1) X2
       have i₂ := eq63 X1 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq22 X3 (M.op X1 X1) X2
       have i₂ := eq63 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq63 eq22
    | exact resolve eq22 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82 (M.op X1 X1) X2
       have i₂ := eq63 X1 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq82 (M.op X1 X1) X2
       have i₂ := eq63 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq63 eq82
    | exact resolve eq82 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq694 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq43
    | exact resolve eq43 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq724 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq694 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq694
    | (have j0 := eq694 X0 X1
       grind)
    | exact resolve eq694 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq1104 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq172 (τ X1) (τ X0)
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq172
    | exact resolve eq172 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1198 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq172 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq1199 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1198 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1263 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (k (τ X0) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1104 X0 X1
       have i₂ := eq1199 (τ X0)
       grind)
    | exact superpose eq1199 eq1104
    | (have j0 := eq1104 X0 X1
       grind)
    | exact resolve eq1104 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1304 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1263 X0 X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1263
    | (have j0 := eq1263 X0 X1
       grind)
    | exact resolve eq1263 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq1315 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1304 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1304
    | (have j0 := eq1304 X0 X1
       grind)
    | exact resolve eq1304 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304
  have eq1318 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1315 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq1315
    | (have j0 := eq1315 X0 X1
       grind)
    | exact resolve eq1315 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1320 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1318 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1318
    | (have j0 := eq1318 X0 X1
       grind)
    | exact resolve eq1318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318
  have eq1321 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1320 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1320
    | (have j0 := eq1320 X0 X1
       grind)
    | exact resolve eq1320 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq1322 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1321 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq1321
    | (have j0 := eq1321 X0 X1
       grind)
    | exact resolve eq1321 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1323 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1199 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1199
    | exact resolve eq1199 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1340 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (k X0 X0)) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 (σ X0) X1
       have i₂ := eq1199 X0
       grind)
    | exact superpose eq1199 eq82
    | exact resolve eq82 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1347 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X1 (σ X0)
       have i₂ := eq1199 X0
       grind)
    | exact superpose eq1199 eq22
    | exact resolve eq22 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1364 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq1323 X0
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1323
    | exact resolve eq1323 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1366 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1364 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1364
    | exact resolve eq1364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364
  have eq1452 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq1366 (τ X0)
       grind)
    | exact superpose eq1366 eq32
    | exact resolve eq32 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1457 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1452 X0
       have i₂ := eq1366 X0
       grind)
    | exact superpose eq1366 eq1452
    | exact resolve eq1452 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452
  have eq1566 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1340 X0 X1
       have i₂ := eq1366 X0
       grind)
    | exact superpose eq1366 eq1340
    | exact resolve eq1340 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq1940 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) X0) = (M.op (M.op X1 X1) (M.op X0 (M.op (σ (M.op X2 X2)) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (σ (M.op X2 X2)) X0) X1 X0
       have i₂ := eq1566 X2 X0
       grind)
    | exact superpose eq1566 eq8
    | exact resolve eq8 eq1566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1976 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (σ (M.op X2 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1940 X0 X1 X2
       have i₂ := eq1566 X2 X0
       grind)
    | exact superpose eq1566 eq1940
    | exact resolve eq1940 eq1566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566 eq1940
  have eq2321 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 X2) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq169 X0 X2 X1
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq169
    | (have j0 := eq169 X0 X1 X1
       have j1 := eq41 X1 X0
       grind)
    | exact resolve eq169 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq169
  have eq2385 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 X2) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2321 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2321
  have eq16372 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (σ X0)) = (σ (k X0 (M.op X1 X1))) ∨ (σ (M.op X1 X1)) = (M.op (M.op X3 X3) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1976 (σ X0) X2 X1
       have i₂ := eq2385 X0 (M.op X1 X1) X3
       grind)
    | exact superpose eq2385 eq1976
    | (have j1 := eq2385 X0 (k X0 (M.op X1 X1)) X2
       grind)
    | exact resolve eq1976 eq2385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1976
  have eq30045 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1322 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq30048 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30045 X0 X1
       have i₂ := eq1366 X0
       grind)
    | exact superpose eq1366 eq30045
    | (have j0 := eq30045 X0 X1
       grind)
    | (have r₁ := eq30045 X0 X0
       have r₂ := eq1366 X0
       grind)
    | exact resolve eq30045 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30045
  have eq36392 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) ≠ (M.op (M.op X0 X0) (σ X1)) ∨ (M.op (M.op X0 X0) (σ X1)) = (k (σ X1) (σ (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30048 (σ X0) (σ (k X0 X0))
       have i₂ := eq1347 X0 X1
       grind)
    | exact superpose eq1347 eq30048
    | (have j0 := eq30048 (σ X1) (M.op X0 X0)
       grind)
    | exact resolve eq30048 eq1347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347 eq30048
  have eq36461 : ∀ X0 X1 : G, (σ (k X1 X1)) ≠ (M.op (M.op X0 X0) (σ X1)) ∨ (M.op (M.op X0 X0) (σ X1)) = (k (σ X1) (σ (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq36392 X0 X1
       have i₂ := eq1199 X1
       grind)
    | exact superpose eq1199 eq36392
    | (have j0 := eq36392 X0 X1
       grind)
    | exact resolve eq36392 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199 eq36392
  have eq36515 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (M.op X0 X0) (σ X1)) = (k (σ X1) (σ (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq36461 X0 X1
       have i₂ := eq1366 X1
       grind)
    | exact superpose eq1366 eq36461
    | (have j0 := eq36461 X0 X1
       grind)
    | exact resolve eq36461 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36461
  have eq36545 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ X1)) = (σ (k X1 (k X1 X1))) ∨ (M.op (M.op X0 X0) (σ X1)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36515 X0 X1
       have i₂ := eq13 X1 (k X1 X1)
       grind)
    | exact superpose eq13 eq36515
    | (have j0 := eq36515 X0 X1
       grind)
    | exact resolve eq36515 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36515
  have eq36558 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ X1)) = (σ (k X1 (M.op X1 X1))) ∨ (M.op (M.op X0 X0) (σ X1)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36545 X0 X1
       have i₂ := eq1366 X1
       grind)
    | exact superpose eq1366 eq36545
    | (have j0 := eq36545 X0 X1
       grind)
    | exact resolve eq36545 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366 eq36545
  have eq36565 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ X1)) = (σ (k X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq36558 X0 X1
       have j1 := eq16372 X1 X1 X0 x
       grind)
    | (have r₁ := eq36558 x X1
       have r₂ := eq16372 X1 X1 x x
       grind)
    | exact resolve eq36558 eq16372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16372 eq36558
  have eq36881 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ (τ X0))) = (σ (k (τ X0) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq36565 X1 (τ X0)
       have i₂ := eq1457 X0
       grind)
    | exact superpose eq1457 eq36565
    | exact resolve eq36565 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36968 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq248 x x (σ X0)
       have i₂ := eq36565 (M.op x x) X0
       grind)
    | exact superpose eq36565 eq248
    | exact resolve eq248 eq36565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36565
  have eq37163 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ (τ X0))) = (k (σ (τ X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36881 X0 X1
       have i₂ := eq16 (M.op X0 X0) (τ X0)
       grind)
    | exact superpose eq16 eq36881
    | exact resolve eq36881 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq36881
  have eq37259 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37163 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq37163
    | exact resolve eq37163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37163
  have eq37734 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq246 x x X1 X0
       have i₂ := eq37259 X0 (M.op x x)
       grind)
    | exact superpose eq37259 eq246
    | exact resolve eq246 eq37259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq37736 : ∀ X0 : G, (M.op X0 (k X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq248 x x X0
       have i₂ := eq37259 X0 (M.op x x)
       grind)
    | exact superpose eq37259 eq248
    | exact resolve eq248 eq37259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq37259
  have eq38412 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (k (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq37736 (τ X0)
       have i₂ := eq1457 X0
       grind)
    | exact superpose eq1457 eq37736
    | exact resolve eq37736 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457 eq37736
  have eq38608 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (k X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq38412 X0
       have i₂ := eq32 (M.op X0 X0) X0
       grind)
    | exact superpose eq32 eq38412
    | exact resolve eq38412 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq38412
  have eq41656 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq36968 X1
       have i₂ := eq37734 X1 X0
       grind)
    | exact superpose eq37734 eq36968
    | exact resolve eq36968 eq37734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36968
  have eq48963 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38608 X1
       have i₂ := eq37734 X1 X0
       grind)
    | exact superpose eq37734 eq38608
    | exact resolve eq38608 eq37734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37734 eq38608
  have eq52873 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48963 (σ X1) (σ X1)
       have i₂ := eq2385 X1 X0 (σ X1)
       grind)
    | exact superpose eq2385 eq48963
    | (have j1 := eq2385 X1 X0 x
       grind)
    | exact resolve eq48963 eq2385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2385 eq48963
  have eq52993 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52873 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq52873
    | (have j0 := eq52873 X0 X1
       grind)
    | exact resolve eq52873 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52873
  have eq53106 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52993 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq52993
    | (have j0 := eq52993 X0 X1
       grind)
    | exact resolve eq52993 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52993
  have eq590737 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq53106 x y
       grind)
    | exact superpose eq53106 eq14
    | (have j1 := eq53106 x y
       grind)
    | exact resolve eq14 eq53106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53106
  have eq590832 : y = (M.op y x) := by
    first
    | (have j1 := eq724 x y
       grind)
    | (have r₁ := eq590737
       have r₂ := eq724 x y
       grind)
    | exact resolve eq590737 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq590737
  have eq591688 : x = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq75 x y
       have i₂ := eq590832
       grind)
    | exact superpose eq590832 eq75
    | exact resolve eq75 eq590832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq591706 : (σ x) = (M.op (σ x) (σ (M.op y x))) := by
    first
    | (have i₁ := eq41656 y x
       have i₂ := eq590832
       grind)
    | exact superpose eq590832 eq41656
    | exact resolve eq41656 eq590832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41656
  have eq591752 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq591706
       have i₂ := eq590832
       grind)
    | exact superpose eq590832 eq591706
    | exact resolve eq591706 eq590832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591706
  have eq591768 : x = (M.op x y) := by
    first
    | (have i₁ := eq591688
       have i₂ := eq590832
       grind)
    | exact superpose eq590832 eq591688
    | exact resolve eq591688 eq590832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590832 eq591688
  have eq604013 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq591752
       grind)
    | exact superpose eq591752 eq14
    | exact resolve eq14 eq591752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591752
  have eq604173 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq604013
       have i₂ := eq591768
       grind)
    | exact superpose eq591768 eq604013
    | exact resolve eq604013 eq591768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591768 eq604013
  have eq604174 : False := by grind
  exact eq604174

/-- `Equation307`: `x ◇ x = x ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation307 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law307 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law307.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
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
  have eq19 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq23 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19
    | exact resolve eq19 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq26 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq31 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq36 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq26 (σ X1) (σ X0)
       grind)
    | exact superpose eq26 eq13
    | (have j1 := eq26 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq49 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq22
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq66 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq23 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq23
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq107 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq36
  have eq124 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq107 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq107
    | exact resolve eq107 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq137 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq28 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq28
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq14
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq538 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq601 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq538
    | (have j0 := eq538 X0 X1
       grind)
    | exact resolve eq538 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq659 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq1180 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq55 x y
       grind)
    | exact superpose eq55 eq14
    | (have j1 := eq55 x y
       grind)
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1187 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8 (σ x)
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq8
    | (have j1 := eq55 X0 X0
       grind)
    | exact resolve eq8 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1405 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq149
       have i₂ := eq659 y x
       grind)
    | exact superpose eq659 eq149
    | (have j1 := eq659 y x
       grind)
    | (have r₁ := eq149
       have r₂ := eq659 y x
       grind)
    | exact resolve eq149 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq1407 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq149
       have i₂ := eq601 y x
       grind)
    | exact superpose eq601 eq149
    | (have j1 := eq601 (σ y) (σ x)
       grind)
    | (have r₁ := eq149
       have r₂ := eq601 y x
       grind)
    | exact resolve eq149 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq1408 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1407
  have eq1410 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq1405
  have eq1422 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq124 x
       have i₂ := eq1408
       grind)
    | exact superpose eq1408 eq124
    | exact resolve eq124 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1425 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 (σ x)
       have i₂ := eq1408
       grind)
    | exact superpose eq1408 eq8
    | exact resolve eq8 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1430 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1422
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1422
    | exact resolve eq1422 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq1510 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq601 y x
       have i₂ := eq1430
       grind)
    | exact superpose eq1430 eq601
    | (have j0 := eq601 y x
       grind)
    | exact resolve eq601 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601 eq1430
  have eq1512 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq1510
  have eq1550 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq1561 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1714 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq137
    | (have j0 := eq137 X1 (τ X0)
       grind)
    | exact resolve eq137 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq1821 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1714 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1714
    | (have j0 := eq1714 X0 X1
       grind)
    | exact resolve eq1714 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1714
  have eq1831 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1821 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1821
    | (have j0 := eq1821 X0 X1
       grind)
    | exact resolve eq1821 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821
  have eq4217 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq124 x
       have i₂ := eq1410
       grind)
    | exact superpose eq1410 eq124
    | exact resolve eq124 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq1410
  have eq4231 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq4217
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4217
    | exact resolve eq4217 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4217
  have eq4232 : x = (k x y) := by grind
  clear eq4231
  have eq5754 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1425
       grind)
    | exact superpose eq1425 eq14
    | exact resolve eq14 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq6256 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5754
       have i₂ := eq1512
       grind)
    | exact superpose eq1512 eq5754
    | exact resolve eq5754 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512 eq5754
  have eq6257 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq6256
  have eq8431 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq66
    | (have j0 := eq66 X1 (σ X0)
       grind)
    | exact resolve eq66 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq8532 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8431 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq8431
    | (have j0 := eq8431 X0 X1
       grind)
    | exact resolve eq8431 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8431
  have eq9840 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1561 x y
       have i₂ := eq4232
       grind)
    | exact superpose eq4232 eq1561
    | (have j0 := eq1561 x y
       grind)
    | exact resolve eq1561 eq4232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561 eq4232
  have eq10463 : (τ (σ y)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq49 (σ x) x
       have i₂ := eq1408
       grind)
    | exact superpose eq1408 eq49
    | exact resolve eq49 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1408
  have eq10821 : (τ (σ y)) = (k (τ (σ x)) x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10463
       have r₂ := eq6257
       grind)
    | exact resolve eq10463 eq6257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10463
  have eq10864 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10821
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq10821
    | exact resolve eq10821 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10821
  have eq10871 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10864
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq10864
    | exact resolve eq10864 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10864
  have eq10903 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8532 x x
       have i₂ := eq10871
       grind)
    | exact superpose eq10871 eq8532
    | exact resolve eq8532 eq10871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8532 eq10871
  have eq10905 : (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq10903
  have eq10916 : y = (M.op x x) := by
    first
    | (have r₁ := eq10905
       have r₂ := eq6257
       grind)
    | exact resolve eq10905 eq6257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6257 eq10905
  have eq11098 : y = (M.op x y) := by
    first
    | (have i₁ := eq8 x
       have i₂ := eq10916
       grind)
    | exact superpose eq10916 eq8
    | exact resolve eq8 eq10916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11102 : x ≠ y ∨ x = (k x x) := by
    first
    | (have i₁ := eq61 x x
       have i₂ := eq10916
       grind)
    | exact superpose eq10916 eq61
    | (have j0 := eq61 x x
       grind)
    | exact resolve eq61 eq10916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq11626 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1180
       have i₂ := eq1831 x y
       grind)
    | exact superpose eq1831 eq1180
    | (have j1 := eq1831 x y
       grind)
    | (have r₁ := eq1180
       have r₂ := eq1831 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1180
       have r₂ := eq1831 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1180 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180 eq1831
  have eq11635 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) ∨ x = y := by grind
  clear eq11626
  have eq11643 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11635
       have i₂ := eq11098
       grind)
    | exact superpose eq11098 eq11635
    | exact resolve eq11635 eq11098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11635
  have eq14240 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1187 x
       have i₂ := eq11643
       grind)
    | exact superpose eq11643 eq1187
    | exact resolve eq1187 eq11643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187 eq11643
  have eq14296 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14240
  have eq14307 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq14296
       have r₂ := eq9840
       grind)
    | exact resolve eq14296 eq9840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9840 eq14296
  have eq14356 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq14307
       grind)
    | exact superpose eq14307 eq14
    | exact resolve eq14 eq14307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14307
  have eq14382 : (σ y) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14356
       have i₂ := eq11098
       grind)
    | exact superpose eq11098 eq14356
    | exact resolve eq14356 eq11098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11098 eq14356
  have eq14383 : x = y := by grind
  clear eq14382
  have eq14780 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq14383
       grind)
    | exact superpose eq14383 eq14
    | exact resolve eq14 eq14383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14788 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1550
       have i₂ := eq14383
       grind)
    | exact superpose eq14383 eq1550
    | exact resolve eq1550 eq14383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550
  have eq14806 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq11102
       have i₂ := eq14383
       grind)
    | exact superpose eq14383 eq11102
    | (have r₁ := eq11102
       have r₂ := eq14383
       grind)
    | exact resolve eq11102 eq14383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11102
  have eq14807 : x = (k x x) := by grind
  clear eq14806
  have eq14816 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14788
       have i₂ := eq10916
       grind)
    | exact superpose eq10916 eq14788
    | exact resolve eq14788 eq10916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14788
  have eq14819 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14780
       have i₂ := eq10916
       grind)
    | exact superpose eq10916 eq14780
    | exact resolve eq14780 eq10916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10916 eq14780
  have eq14820 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14816
       have i₂ := eq14807
       grind)
    | exact superpose eq14807 eq14816
    | exact resolve eq14816 eq14807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14807 eq14816
  have eq14823 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14819
       have i₂ := eq14383
       grind)
    | exact superpose eq14383 eq14819
    | exact resolve eq14819 eq14383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14819
  have eq14824 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14820
       have i₂ := eq14383
       grind)
    | exact superpose eq14383 eq14820
    | exact resolve eq14820 eq14383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14383 eq14820
  have eq14825 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq14824
  have eq14828 : False := by grind
  exact eq14828

/-- `Equation307`: `x ◇ x = x ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pyx_Equation307 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law307 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law307.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq24 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq26 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq27 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq29 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq38 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
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
  have eq43 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq24 (σ X1) (σ X0)
       grind)
    | exact superpose eq24 eq13
    | (have j1 := eq24 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq50 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X0
       have i₂ := eq24 X1 (σ X0)
       grind)
    | exact superpose eq24 eq21
    | (have j1 := eq24 X1 (σ X0)
       grind)
    | exact resolve eq21 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq24
  have eq56 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq48
    | exact resolve eq48 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq25
    | exact resolve eq25 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq25 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq102 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X1
       have i₂ := eq12 X0 (τ X1)
       grind)
    | (have i₁ := eq38 X0
       have i₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq12 eq38
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq137 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X0
       have i₂ := eq12 X0 (σ X0)
       grind)
    | (have i₁ := eq26 X0 X1
       have i₂ := eq12 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq12 eq26
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq26 x y
       grind)
    | exact superpose eq26 eq14
    | (have j1 := eq26 x y
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq538 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq27
    | exact resolve eq27 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq601 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq538
    | (have j0 := eq538 X0 X1
       grind)
    | exact resolve eq538 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq659 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq1180 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq57 y x
       grind)
    | exact superpose eq57 eq14
    | (have j1 := eq57 y x
       grind)
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1187 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8 (σ X0)
       have i₂ := eq57 X0 X0
       grind)
    | exact superpose eq57 eq8
    | (have j1 := eq57 X0 X0
       grind)
    | exact resolve eq8 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1406 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq149
       have i₂ := eq659 y x
       grind)
    | exact superpose eq659 eq149
    | (have j1 := eq659 y x
       grind)
    | (have r₁ := eq149
       have r₂ := eq659 y x
       grind)
    | exact resolve eq149 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq1408 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq149
       have i₂ := eq601 y x
       grind)
    | exact superpose eq601 eq149
    | (have j1 := eq601 (σ y) (σ x)
       grind)
    | (have r₁ := eq149
       have r₂ := eq601 y x
       grind)
    | exact resolve eq149 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq1409 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1408
  have eq1411 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by grind
  clear eq1406
  have eq1423 : x = (k (τ (σ y)) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq1409
       grind)
    | exact superpose eq1409 eq56
    | exact resolve eq56 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1426 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 (σ x)
       have i₂ := eq1409
       grind)
    | exact superpose eq1409 eq8
    | exact resolve eq8 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1431 : x = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1423
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1423
    | exact resolve eq1423 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423
  have eq1512 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq601 y x
       have i₂ := eq1431
       grind)
    | exact superpose eq1431 eq601
    | (have j0 := eq601 y x
       grind)
    | exact resolve eq601 eq1431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601 eq1431
  have eq1514 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq1512
  have eq1552 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq1563 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1716 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq137
    | (have j0 := eq137 X1 (τ X0)
       grind)
    | exact resolve eq137 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq1823 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1716 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1716
    | (have j0 := eq1716 X0 X1
       grind)
    | exact resolve eq1716 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1716
  have eq1833 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1823 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1823
    | (have j0 := eq1823 X0 X1
       grind)
    | exact resolve eq1823 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823
  have eq4235 : x = (k (τ (σ y)) x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq1411
       grind)
    | exact superpose eq1411 eq56
    | exact resolve eq56 eq1411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1411
  have eq4249 : x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq4235
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4235
    | exact resolve eq4235 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4235
  have eq4250 : x = (k y x) := by grind
  clear eq4249
  have eq5754 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1426
       grind)
    | exact superpose eq1426 eq14
    | exact resolve eq14 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq6230 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5754
       have i₂ := eq1514
       grind)
    | exact superpose eq1514 eq5754
    | exact resolve eq5754 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1514 eq5754
  have eq6231 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq6230
  have eq8877 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq102 X1 (σ X0)
       grind)
    | exact superpose eq102 eq13
    | (have j1 := eq102 X1 (σ X0)
       grind)
    | exact resolve eq13 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq8954 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8877 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq8877
    | (have j0 := eq8877 X0 X1
       grind)
    | exact resolve eq8877 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8877
  have eq9688 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1563 x y
       have i₂ := eq4250
       grind)
    | exact superpose eq4250 eq1563
    | (have j0 := eq1563 x y
       grind)
    | exact resolve eq1563 eq4250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563 eq4250
  have eq10309 : (τ (σ y)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq50 x (σ x)
       have i₂ := eq1409
       grind)
    | exact superpose eq1409 eq50
    | exact resolve eq50 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1409
  have eq10358 : (τ (σ y)) = (k (τ (σ x)) x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10309
       have r₂ := eq6231
       grind)
    | exact resolve eq10309 eq6231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10309
  have eq10384 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10358
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq10358
    | exact resolve eq10358 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10358
  have eq10391 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10384
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq10384
    | exact resolve eq10384 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10384
  have eq10422 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8954 x x
       have i₂ := eq10391
       grind)
    | exact superpose eq10391 eq8954
    | exact resolve eq8954 eq10391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8954 eq10391
  have eq10424 : (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq10422
  have eq10435 : y = (M.op x x) := by
    first
    | (have r₁ := eq10424
       have r₂ := eq6231
       grind)
    | exact resolve eq10424 eq6231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6231 eq10424
  have eq10614 : y = (M.op x y) := by
    first
    | (have i₁ := eq8 x
       have i₂ := eq10435
       grind)
    | exact superpose eq10435 eq8
    | exact resolve eq8 eq10435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10616 : x ≠ y ∨ x = (k x x) := by
    first
    | (have i₁ := eq63 x x
       have i₂ := eq10435
       grind)
    | exact superpose eq10435 eq63
    | (have j0 := eq63 x x
       grind)
    | exact resolve eq63 eq10435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq11459 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1180
       have i₂ := eq1833 x y
       grind)
    | exact superpose eq1833 eq1180
    | (have j1 := eq1833 x y
       grind)
    | (have r₁ := eq1180
       have r₂ := eq1833 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1180
       have r₂ := eq1833 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1180 eq1833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180 eq1833
  have eq11468 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) ∨ x = y := by grind
  clear eq11459
  have eq11476 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11468
       have i₂ := eq10614
       grind)
    | exact superpose eq10614 eq11468
    | exact resolve eq11468 eq10614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11468
  have eq14076 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1187 x
       have i₂ := eq11476
       grind)
    | exact superpose eq11476 eq1187
    | exact resolve eq1187 eq11476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187 eq11476
  have eq14132 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14076
  have eq14144 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq14132
       have r₂ := eq9688
       grind)
    | exact resolve eq14132 eq9688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9688 eq14132
  have eq14191 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq14144
       grind)
    | exact superpose eq14144 eq14
    | exact resolve eq14 eq14144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14144
  have eq14217 : (σ y) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14191
       have i₂ := eq10614
       grind)
    | exact superpose eq10614 eq14191
    | exact resolve eq14191 eq10614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10614 eq14191
  have eq14218 : x = y := by grind
  clear eq14217
  have eq14621 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq14218
       grind)
    | exact superpose eq14218 eq14
    | exact resolve eq14 eq14218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14629 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1552
       have i₂ := eq14218
       grind)
    | exact superpose eq14218 eq1552
    | exact resolve eq1552 eq14218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq14646 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq10616
       have i₂ := eq14218
       grind)
    | exact superpose eq14218 eq10616
    | (have r₁ := eq10616
       have r₂ := eq14218
       grind)
    | exact resolve eq10616 eq14218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10616
  have eq14649 : x = (k x x) := by grind
  clear eq14646
  have eq14657 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14629
       have i₂ := eq10435
       grind)
    | exact superpose eq10435 eq14629
    | exact resolve eq14629 eq10435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14629
  have eq14660 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14621
       have i₂ := eq10435
       grind)
    | exact superpose eq10435 eq14621
    | exact resolve eq14621 eq10435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10435 eq14621
  have eq14661 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14657
       have i₂ := eq14649
       grind)
    | exact superpose eq14649 eq14657
    | exact resolve eq14657 eq14649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14649 eq14657
  have eq14664 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14660
       have i₂ := eq14218
       grind)
    | exact superpose eq14218 eq14660
    | exact resolve eq14660 eq14218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14660
  have eq14665 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14661
       have i₂ := eq14218
       grind)
    | exact superpose eq14218 eq14661
    | exact resolve eq14661 eq14218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14218 eq14661
  have eq14666 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq14665
  have eq14671 : False := by grind
  exact eq14671

/-- `Equation309`: `x ◇ x = x ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation309 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law309 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law309.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X0)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq27 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq52 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq23
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq28 (σ X1) (σ X0)
       grind)
    | exact superpose eq28 eq13
    | (have j1 := eq28 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq67 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq24 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq97 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq37
  have eq112 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq97 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq97
    | exact resolve eq97 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq151 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq29 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq29
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29 x y
       grind)
    | exact superpose eq29 eq14
    | (have j1 := eq29 x y
       grind)
    | exact resolve eq14 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq29 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq572 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq10
    | (have j1 := eq32 X0 X1
       grind)
    | exact resolve eq10 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq641 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq572 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq572
    | (have j0 := eq572 X0 X1
       grind)
    | exact resolve eq572 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq1079 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq40 X0 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq40 X0 X0
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1089 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X1) (σ X0)
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq8
    | (have j1 := eq40 X0 X1
       grind)
    | exact resolve eq8 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1422 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq163
       have i₂ := eq641 y x
       grind)
    | exact superpose eq641 eq163
    | (have j1 := eq641 (σ y) (σ x)
       grind)
    | (have r₁ := eq163
       have r₂ := eq641 y x
       grind)
    | exact resolve eq163 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq1423 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1422
  have eq1437 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq112 x
       have i₂ := eq1423
       grind)
    | exact superpose eq1423 eq112
    | exact resolve eq112 eq1423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1446 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 (σ x) (σ x)
       have i₂ := eq1423
       grind)
    | exact superpose eq1423 eq8
    | exact resolve eq8 eq1423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1449 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1437
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1437
    | exact resolve eq1437 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437
  have eq1529 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq641 y x
       have i₂ := eq1449
       grind)
    | exact superpose eq1449 eq641
    | (have j0 := eq641 y x
       grind)
    | exact resolve eq641 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq1449
  have eq1531 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq1529
  have eq1569 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq63 x y
       grind)
    | exact superpose eq63 eq14
    | (have j1 := eq63 x y
       grind)
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1585 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4098 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1446
       grind)
    | exact superpose eq1446 eq14
    | exact resolve eq14 eq1446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq4433 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4098
       have i₂ := eq1531
       grind)
    | exact superpose eq1531 eq4098
    | exact resolve eq4098 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1531 eq4098
  have eq4434 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq4433
  have eq10518 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq67
    | (have j0 := eq67 X1 (σ X0)
       grind)
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10544 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq184 (τ X0)
       have i₂ := eq67 (τ X0) X0
       grind)
    | exact superpose eq67 eq184
    | (have j0 := eq184 (τ X0)
       have j1 := eq67 (τ X0) X0
       grind)
    | exact resolve eq184 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq184
  have eq10609 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10544 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10544
    | (have j0 := eq10544 X0
       grind)
    | exact resolve eq10544 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10544
  have eq10625 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10518 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq10518
    | (have j0 := eq10518 X0 X1
       grind)
    | exact resolve eq10518 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10518
  have eq10645 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10609 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10609
    | (have j0 := eq10609 X0
       grind)
    | exact resolve eq10609 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10609
  have eq10670 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq10645 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10645
    | (have j0 := eq10645 X0
       grind)
    | exact resolve eq10645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10645
  have eq10688 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10670 X0
       have j1 := eq45 X0 X0
       grind)
    | (have r₁ := eq10670 x
       have r₂ := eq45 x x
       grind)
    | exact resolve eq10670 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq10670
  have eq10705 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10688 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq10688
    | (have j0 := eq10688 (σ X0)
       grind)
    | exact resolve eq10688 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10688
  have eq10744 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10705 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq10705
    | (have j0 := eq10705 X0
       grind)
    | exact resolve eq10705 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10705
  have eq12873 : (τ (σ y)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq52 (σ x) x
       have i₂ := eq1423
       grind)
    | exact superpose eq1423 eq52
    | exact resolve eq52 eq1423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1423
  have eq13293 : (τ (σ y)) = (k (τ (σ x)) x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12873
       have r₂ := eq4434
       grind)
    | exact resolve eq12873 eq4434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12873
  have eq13339 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13293
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq13293
    | exact resolve eq13293 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13293
  have eq13348 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13339
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq13339
    | exact resolve eq13339 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13339
  have eq13385 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10625 x x
       have i₂ := eq13348
       grind)
    | exact superpose eq13348 eq10625
    | exact resolve eq10625 eq13348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13348
  have eq13387 : (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq13385
  have eq13398 : y = (M.op x x) := by
    first
    | (have r₁ := eq13387
       have r₂ := eq4434
       grind)
    | exact resolve eq13387 eq4434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4434 eq13387
  have eq13585 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq10744 x
       have i₂ := eq13398
       grind)
    | exact superpose eq13398 eq10744
    | (have j0 := eq10744 x
       grind)
    | exact resolve eq10744 eq13398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10744
  have eq13586 : y = (M.op x y) := by
    first
    | (have i₁ := eq8 x x
       have i₂ := eq13398
       grind)
    | exact superpose eq13398 eq8
    | exact resolve eq8 eq13398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13892 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq613 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq13893 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq13892 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13892
    | (have j0 := eq13892 X0
       grind)
    | exact resolve eq13892 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13892
  have eq16613 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq13893 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq13893
    | (have j0 := eq13893 (σ X0)
       grind)
    | exact resolve eq13893 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13893
  have eq16628 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16613 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq16613
    | (have j0 := eq16613 X0
       grind)
    | exact resolve eq16613 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16613
  have eq26331 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq16628 X0
       have i₂ := eq10625 X0 X0
       grind)
    | exact superpose eq10625 eq16628
    | (have j0 := eq16628 X0
       have j1 := eq10625 X0 X0
       grind)
    | (have r₁ := eq16628 x
       have r₂ := eq10625 x x
       grind)
    | exact resolve eq16628 eq10625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10625 eq16628
  have eq26360 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq26331 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26331
  have eq27077 : y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26360 x
       have i₂ := eq13398
       grind)
    | exact superpose eq13398 eq26360
    | exact resolve eq26360 eq13398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13398 eq26360
  have eq28782 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1089 x x
       have i₂ := eq27077
       grind)
    | exact superpose eq27077 eq1089
    | exact resolve eq1089 eq27077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089 eq27077
  have eq28880 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq28782
  have eq57597 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1079 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq57598 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq57597 X0 X1
       have j1 := eq151 X1 X0
       grind)
    | (have r₁ := eq57597 (k X1 X1) X0
       have r₂ := eq151 X0 X1
       grind)
    | (have r₁ := eq57597 X0 (σ (k X1 X1))
       have r₂ := eq151 (σ X0) X1
       grind)
    | (have r₁ := eq57597 X1 X0
       have r₂ := eq151 X0 X1
       grind)
    | exact resolve eq57597 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq57597
  have eq57789 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X1)
       have i₂ := eq57598 (τ X1) X0
       grind)
    | (have i₁ := eq17 X0 X1
       have i₂ := eq57598 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq57598 eq17
    | (have j1 := eq57598 (τ X1) X0
       grind)
    | exact resolve eq17 eq57598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq57598
  have eq57875 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57789 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq57789
    | (have j0 := eq57789 X0 X1
       grind)
    | exact resolve eq57789 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57789
  have eq57889 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57875 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq57875
    | (have j0 := eq57875 X0 X1
       grind)
    | exact resolve eq57875 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57875
  have eq58109 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1569
       have i₂ := eq57889 y x
       grind)
    | exact superpose eq57889 eq1569
    | (have j1 := eq57889 y x
       grind)
    | exact resolve eq1569 eq57889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569 eq57889
  have eq58238 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by grind
  clear eq58109
  have eq58321 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq58238
       grind)
    | exact superpose eq58238 eq14
    | exact resolve eq14 eq58238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58238
  have eq58366 : (σ y) ≠ (σ y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq58321
       have i₂ := eq13586
       grind)
    | exact superpose eq13586 eq58321
    | exact resolve eq58321 eq13586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58321
  have eq58367 : y = (k x x) := by grind
  clear eq58366
  have eq58487 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1585 x x
       have i₂ := eq58367
       grind)
    | exact superpose eq58367 eq1585
    | (have j0 := eq1585 x x
       grind)
    | exact resolve eq1585 eq58367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585
  have eq98328 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq28880
       grind)
    | exact superpose eq28880 eq14
    | exact resolve eq14 eq28880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28880
  have eq98347 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq98328
       have i₂ := eq13586
       grind)
    | exact superpose eq13586 eq98328
    | exact resolve eq98328 eq13586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98328
  have eq99782 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq98347
       have i₂ := eq40 x x
       grind)
    | exact superpose eq40 eq98347
    | (have j1 := eq40 x x
       grind)
    | exact resolve eq98347 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq99783 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq98347
       have i₂ := eq63 x x
       grind)
    | exact superpose eq63 eq98347
    | (have j1 := eq63 x x
       grind)
    | exact resolve eq98347 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq98347
  have eq99797 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq99783
       have r₂ := eq58487
       grind)
    | exact resolve eq99783 eq58487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58487 eq99783
  have eq99798 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have r₁ := eq99782
       have r₂ := eq13585
       grind)
    | exact resolve eq99782 eq13585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13585 eq99782
  have eq99804 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq99797
       have i₂ := eq58367
       grind)
    | exact superpose eq58367 eq99797
    | exact resolve eq99797 eq58367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99797
  have eq99805 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq99804
  have eq99806 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq99798
       have i₂ := eq58367
       grind)
    | exact superpose eq58367 eq99798
    | exact resolve eq99798 eq58367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99798
  have eq99807 : (σ x) = (σ (k x x)) := by grind
  clear eq99806
  have eq99811 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq99807
       have i₂ := eq58367
       grind)
    | exact superpose eq58367 eq99807
    | exact resolve eq99807 eq58367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58367 eq99807
  have eq101887 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq99811
       grind)
    | exact superpose eq99811 eq14
    | exact resolve eq14 eq99811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102154 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq101887
       have i₂ := eq99805
       grind)
    | exact superpose eq99805 eq101887
    | exact resolve eq101887 eq99805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99805 eq101887
  have eq102175 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq102154
       have i₂ := eq13586
       grind)
    | exact superpose eq13586 eq102154
    | exact resolve eq102154 eq13586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13586 eq102154
  have eq102194 : False := by grind
  exact eq102194

/-- `Equation310`: `x ◇ x = x ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation310 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law310 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law310.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X1)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2
       have i₂ := eq8 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X1 X1) X1
       have i₂ := eq8 (M.op X1 X1) X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X0
       have i₂ := eq8 X0 X1
       grind)
    | (have i₁ := eq8 X0 (M.op X1 X1)
       have i₂ := eq8 (M.op X1 X1) X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X1 X1))) = X0 := by
    intro X0 X1
    grind
  have eq22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 (M.op X1 X0)
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
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
  have eq36 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq41 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq43 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36
    | exact resolve eq36 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq45 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq23
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41
    | exact resolve eq41 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq96 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq43 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq43
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq146 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq50
  have eq163 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq146 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq146
    | exact resolve eq146 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq166 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq31
    | exact resolve eq31 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 (M.op X1 X1)
       have i₂ := eq8 X0 X1
       grind)
    | (have i₁ := eq175 X0 X0
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq175
    | (have j0 := eq175 X0 X0
       grind)
    | exact resolve eq175 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq29 (σ y) (σ x) X0
       grind)
    | exact superpose eq29 eq14
    | (have j1 := eq29 (σ y) x X0
       grind)
    | exact resolve eq14 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq299 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq163 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq163 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq163
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq163 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq427 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq8
    | (have j1 := eq34 X0 X0
       grind)
    | exact resolve eq8 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq457 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ X0)) ∨ (σ (k X3 X0)) = (M.op (σ X3) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X2 (σ X3)
       have i₂ := eq34 X3 X0
       grind)
    | exact superpose eq34 eq16
    | (have j1 := eq34 X3 X0
       grind)
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ X0)) = X3 ∨ (k X1 X3) = (M.op X1 X3) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30 X3 X1 (σ X2)
       have i₂ := eq34 X2 X0
       grind)
    | exact superpose eq34 eq30
    | (have j0 := eq30 X3 X1 X2
       have j1 := eq34 X2 X0
       grind)
    | exact resolve eq30 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq465 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq2626 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq465 (τ X0)
       have i₂ := eq23 X0 (τ X0)
       grind)
    | exact superpose eq23 eq465
    | (have j0 := eq465 (τ X0)
       grind)
    | exact resolve eq465 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2628 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2626 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2626
    | (have j0 := eq2626 X0
       grind)
    | exact resolve eq2626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2626
  have eq2631 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2628 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2628
    | (have j0 := eq2628 X0
       grind)
    | exact resolve eq2628 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2628
  have eq2643 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2631 (τ X0)
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq2631
    | (have j0 := eq2631 (τ X0)
       grind)
    | exact resolve eq2631 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq2631
  have eq2678 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq45
    | exact resolve eq45 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2786 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq10
    | (have j1 := eq45 X0 X1
       grind)
    | exact resolve eq10 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq2822 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2678 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2678
    | (have j0 := eq2678 X0 X1
       grind)
    | exact resolve eq2678 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2678
  have eq2914 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq4729 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ X0)
       have i₂ := eq166 X0 X0
       grind)
    | exact superpose eq166 eq8
    | (have j1 := eq166 X0 X0
       grind)
    | exact resolve eq8 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq5376 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq96
    | (have j0 := eq96 X1 (σ X0)
       grind)
    | exact resolve eq96 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq5465 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5376 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq5376
    | (have j0 := eq5376 X0 X1
       grind)
    | exact resolve eq5376 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5376
  have eq5523 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq425
       have i₂ := eq2914 y x
       grind)
    | exact superpose eq2914 eq425
    | (have j1 := eq2914 y x
       grind)
    | (have r₁ := eq425
       have r₂ := eq2914 y x
       grind)
    | exact resolve eq425 eq2914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2914
  have eq5524 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq425
       have i₂ := eq2822 y x
       grind)
    | exact superpose eq2822 eq425
    | (have j1 := eq2822 (σ y) (σ x)
       grind)
    | (have r₁ := eq425
       have r₂ := eq2822 y x
       grind)
    | exact resolve eq425 eq2822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq5525 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq5524
  have eq5526 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq5523
  have eq6161 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq163 x
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq163
    | exact resolve eq163 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6164 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ x)
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq8
    | exact resolve eq8 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6169 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (σ y))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (σ x) X0
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq17
    | exact resolve eq17 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq6206 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6161
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6161
    | exact resolve eq6161 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6161
  have eq6579 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq6206
       grind)
    | exact superpose eq6206 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq6206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6583 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2822 y x
       have i₂ := eq6206
       grind)
    | exact superpose eq6206 eq2822
    | (have j0 := eq2822 y x
       grind)
    | exact resolve eq2822 eq6206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822 eq6206
  have eq6584 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq6583
  have eq6585 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq6579
  have eq8105 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq163 x
       have i₂ := eq5526
       grind)
    | exact superpose eq5526 eq163
    | exact resolve eq163 eq5526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq5526
  have eq8155 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq8105
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq8105
    | exact resolve eq8105 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8105
  have eq8156 : x = (k x y) := by grind
  clear eq8155
  have eq9481 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq441 x x
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq441
    | exact resolve eq441 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq9546 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9481
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq9481
    | exact resolve eq9481 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9481
  have eq11531 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (M.op X1 X1)) = (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 (τ X0)
       have i₂ := eq427 (τ X0) X1
       grind)
    | exact superpose eq427 eq23
    | (have j1 := eq427 (τ X0) X1
       grind)
    | exact resolve eq23 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq427
  have eq11666 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11531 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11531
    | (have j0 := eq11531 X0 X1
       grind)
    | exact resolve eq11531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11531
  have eq11693 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11666 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11666
    | (have j0 := eq11666 X0 X1
       grind)
    | exact resolve eq11666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11666
  have eq13991 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq457 y X0 X1 x
       grind)
    | exact superpose eq457 eq14
    | (have j1 := eq457 y X0 X1 x
       grind)
    | exact resolve eq14 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq14093 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13991 X0 X1
       have i₂ := eq8156
       grind)
    | exact superpose eq8156 eq13991
    | (have j0 := eq13991 X0 X1
       grind)
    | exact resolve eq13991 eq8156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13991
  have eq15967 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 (M.op X1 X1)
       have i₂ := eq11693 X0 X1
       grind)
    | exact superpose eq11693 eq175
    | (have j0 := eq175 X0 (M.op X1 X1)
       have j1 := eq11693 X0 X1
       grind)
    | (have r₁ := eq175 X0 X0
       have r₂ := eq11693 X0 X1
       grind)
    | exact resolve eq175 eq11693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11693
  have eq16082 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq15967 X0 X1
       have j1 := eq185 X0 X1
       grind)
    | (have r₁ := eq15967 (M.op X1 X1) X1
       have r₂ := eq185 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq15967 X0 X1
       have r₂ := eq185 X0 X1
       grind)
    | exact resolve eq15967 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq15967
  have eq24532 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq463 y X0 x X1
       grind)
    | exact superpose eq463 eq14
    | (have j1 := eq463 y X0 x X1
       grind)
    | (have r₁ := eq14
       have r₂ := eq463 y (σ x) x (σ (M.op x y))
       grind)
    | exact resolve eq14 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq24660 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 (σ y)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24532 X0 X1
       have i₂ := eq8156
       grind)
    | exact superpose eq8156 eq24532
    | (have j0 := eq24532 X0 X1
       grind)
    | exact resolve eq24532 eq8156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24532
  have eq46085 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq2786 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786
  have eq46086 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq46085 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46085
    | (have j0 := eq46085 X0
       grind)
    | exact resolve eq46085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46085
  have eq46213 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq46086 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq46086
    | (have j0 := eq46086 X0
       have j1 := eq31 X0 X0
       grind)
    | (have r₁ := eq46086 X0
       have r₂ := eq31 X0 X0
       grind)
    | exact resolve eq46086 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46242 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq46086 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq46086
    | (have j0 := eq46086 (σ X0)
       grind)
    | exact resolve eq46086 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46249 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46242 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq46242
    | (have j0 := eq46242 X0
       grind)
    | exact resolve eq46242 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46242
  have eq46254 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq46213 X0
       have j1 := eq46086 X0
       grind)
    | (have r₁ := eq46213 X0
       have r₂ := eq46086 X0
       grind)
    | exact resolve eq46213 eq46086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46086 eq46213
  have eq50877 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq46249 X0
       have i₂ := eq5465 X0 X0
       grind)
    | exact superpose eq5465 eq46249
    | (have j0 := eq46249 X0
       have j1 := eq5465 X0 X0
       grind)
    | (have r₁ := eq46249 x
       have r₂ := eq5465 x x
       grind)
    | exact resolve eq46249 eq5465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5465 eq46249
  have eq50895 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq50877 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50877
  have eq65868 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2643 (σ X0)
       have i₂ := eq299 (σ X0) X0
       grind)
    | exact superpose eq299 eq2643
    | (have j0 := eq2643 (σ X0)
       have j1 := eq299 (σ X0) X0
       grind)
    | exact resolve eq2643 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299 eq2643
  have eq65905 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq65868 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq65868
    | (have j0 := eq65868 X0
       grind)
    | exact resolve eq65868 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65868
  have eq65917 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq65905 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq65905
    | (have j0 := eq65905 X0
       grind)
    | exact resolve eq65905 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65905
  have eq65921 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq65917 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq65917
    | (have j0 := eq65917 X0
       grind)
    | exact resolve eq65917 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65917
  have eq65924 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq65921 X0
       have j1 := eq175 X0 X0
       grind)
    | (have r₁ := eq65921 x
       have r₂ := eq175 x x
       grind)
    | exact resolve eq65921 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq65921
  have eq66663 : x ≠ (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq65924 x
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq65924
    | (have j0 := eq65924 x
       grind)
    | exact resolve eq65924 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65924
  have eq66736 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66663
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq66663
    | exact resolve eq66663 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66663
  have eq81580 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq9546
       grind)
    | exact superpose eq9546 eq9
    | exact resolve eq9 eq9546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9546
  have eq81590 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq81580
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq81580
    | exact resolve eq81580 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81580
  have eq81934 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq31 x x
       have i₂ := eq81590
       grind)
    | exact superpose eq81590 eq31
    | exact resolve eq31 eq81590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq81590
  have eq81947 : y = (M.op x x) ∨ x = y := by grind
  clear eq81934
  have eq81968 : ∀ X0 : G, (k X0 (M.op X0 y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq81947
       grind)
    | exact superpose eq81947 eq18
    | exact resolve eq18 eq81947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq81947
  have eq82589 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq81968 x
       have i₂ := eq6585
       grind)
    | exact superpose eq6585 eq81968
    | exact resolve eq81968 eq6585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6585 eq81968
  have eq82645 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq82589
       have r₂ := eq66736
       grind)
    | exact resolve eq82589 eq66736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66736 eq82589
  have eq82810 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq465 x
       have i₂ := eq82645
       grind)
    | exact superpose eq82645 eq465
    | (have j0 := eq465 x
       grind)
    | exact resolve eq465 eq82645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq82831 : ∀ X0 : G, x ≠ x ∨ x = (k x (M.op X0 X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq16082 x X0
       have i₂ := eq82645
       grind)
    | exact superpose eq82645 eq16082
    | (have j0 := eq16082 x X0
       grind)
    | (have r₁ := eq16082 x x
       have r₂ := eq82645
       grind)
    | exact resolve eq16082 eq82645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16082 eq82645
  have eq82863 : ∀ X0 : G, x = (k x (M.op X0 X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq82831 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82831
  have eq82868 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq82810
  have eq85789 : x = (k x (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82863 (σ x)
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq82863
    | exact resolve eq82863 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82863
  have eq85807 : x = (k x (σ y)) ∨ y = (M.op x x) := by grind
  clear eq85789
  have eq88190 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq219 X0
       have i₂ := eq82868
       grind)
    | exact superpose eq82868 eq219
    | (have j0 := eq219 X0
       grind)
    | exact resolve eq219 eq82868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq88191 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5525
       have i₂ := eq82868
       grind)
    | exact superpose eq82868 eq5525
    | exact resolve eq5525 eq82868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5525
  have eq88300 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq88191
  have eq88314 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq88190 X0
       grind)
    | (have r₁ := eq88190 X0
       have r₂ := eq6584
       grind)
    | exact resolve eq88190 eq6584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88190
  have eq88604 : (σ x) = (σ y) ∨ y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50895 x
       have i₂ := eq88300
       grind)
    | exact superpose eq88300 eq50895
    | exact resolve eq50895 eq88300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50895 eq88300
  have eq88622 : y = (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq88604
  have eq88936 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq4729 x x
       have i₂ := eq88622
       grind)
    | exact superpose eq88622 eq4729
    | exact resolve eq4729 eq88622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4729 eq88622
  have eq88984 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq88936 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88936
  have eq90564 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1
       have i₂ := eq88984 X0
       grind)
    | (have i₁ := eq8 (σ y) X1
       have i₂ := eq88984 (σ y)
       grind)
    | exact superpose eq88984 eq8
    | exact resolve eq8 eq88984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90566 : ∀ X0 X1 : G, (M.op X0 (σ y)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq88984 X0
       grind)
    | (have i₁ := eq12 (σ y) X1
       have i₂ := eq88984 (σ y)
       grind)
    | exact superpose eq88984 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq88984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88984
  have eq99113 : x = (M.op x (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85807
       have i₂ := eq88314 x
       grind)
    | exact superpose eq88314 eq85807
    | exact resolve eq85807 eq88314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85807 eq88314
  have eq99127 : x = (M.op x (σ y)) ∨ y = (M.op x x) := by grind
  clear eq99113
  have eq99139 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6169 X0 x
       have i₂ := eq99127
       grind)
    | exact superpose eq99127 eq6169
    | exact resolve eq6169 eq99127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6169 eq99127
  have eq99173 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq99139 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99139
  have eq99479 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6164 X0
       have i₂ := eq99173 X0
       grind)
    | (have i₁ := eq6164 x
       have i₂ := eq99173 x
       grind)
    | exact superpose eq99173 eq6164
    | exact resolve eq6164 eq99173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6164
  have eq99658 : (σ x) = (M.op (σ x) x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82868
       have i₂ := eq99173 (σ x)
       grind)
    | exact superpose eq99173 eq82868
    | exact resolve eq82868 eq99173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82868 eq99173
  have eq99758 : (σ x) = (M.op (σ x) x) ∨ y = (M.op x x) := by grind
  clear eq99658
  have eq99781 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq99479 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99479
  have eq103177 : (σ (M.op x y)) ≠ (M.op (σ x) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq99781 (σ x)
       grind)
    | exact superpose eq99781 eq14
    | exact resolve eq14 eq99781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99781
  have eq108456 : (σ x) ≠ (M.op (σ x) x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq103177
       have i₂ := eq6584
       grind)
    | exact superpose eq6584 eq103177
    | exact resolve eq103177 eq6584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6584 eq103177
  have eq108457 : (σ x) ≠ (M.op (σ x) x) ∨ y = (M.op x x) := by grind
  clear eq108456
  have eq108459 : y = (M.op x x) := by
    first
    | (have r₁ := eq108457
       have r₂ := eq99758
       grind)
    | exact resolve eq108457 eq99758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99758 eq108457
  have eq108499 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x
       have i₂ := eq108459
       grind)
    | exact superpose eq108459 eq8
    | exact resolve eq8 eq108459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108502 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq108459
       grind)
    | exact superpose eq108459 eq16
    | exact resolve eq16 eq108459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq109054 : ∀ X0 : G, (M.op X0 y) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq46254 X0
       have i₂ := eq108499 X0
       grind)
    | (have i₁ := eq46254 y
       have i₂ := eq108499 y
       grind)
    | exact superpose eq108499 eq46254
    | (have j0 := eq46254 X0
       grind)
    | exact resolve eq46254 eq108499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46254
  have eq109469 : ∀ X0 X1 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14093 X0 X1
       have i₂ := eq108499 x
       grind)
    | exact superpose eq108499 eq14093
    | (have j0 := eq14093 X0 X1
       grind)
    | exact resolve eq14093 eq108499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14093
  have eq109472 : ∀ X0 X1 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ y)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24660 X0 X1
       have i₂ := eq108499 x
       grind)
    | exact superpose eq108499 eq24660
    | (have j0 := eq24660 X0 X1
       grind)
    | exact resolve eq24660 eq108499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24660
  have eq109479 : ∀ X0 X1 : G, (σ x) ≠ (σ y) ∨ (M.op X0 (σ y)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq109472 X0 X1
       have i₂ := eq108459
       grind)
    | exact superpose eq108459 eq109472
    | (have j0 := eq109472 X0 X1
       grind)
    | exact resolve eq109472 eq108459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109472
  have eq109482 : ∀ X0 X1 : G, (σ x) ≠ (σ y) ∨ (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq109469 X0 X1
       have i₂ := eq108459
       grind)
    | exact superpose eq108459 eq109469
    | (have j0 := eq109469 X0 X1
       grind)
    | exact resolve eq109469 eq108459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109469
  have eq109524 : ∀ X0 : G, (M.op X0 y) ≠ X0 ∨ (σ (M.op (τ X0) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq109054 X0
       have i₂ := eq108499 (τ X0)
       grind)
    | exact superpose eq108499 eq109054
    | (have j0 := eq109054 X0
       grind)
    | exact resolve eq109054 eq108499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109054
  have eq109578 : ∀ X0 X1 : G, (M.op X0 (σ y)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq109479 X0 X1
       have j1 := eq90566 X0 X1
       grind)
    | (have r₁ := eq109479 X0 X1
       have r₂ := eq90566 X0 X1
       grind)
    | exact resolve eq109479 eq90566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90566 eq109479
  have eq109579 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq109482 X0 X1
       have j1 := eq90564 X0 X1
       grind)
    | (have r₁ := eq109482 X0 X1
       have r₂ := eq90564 X0 X1
       grind)
    | exact resolve eq109482 eq90564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90564 eq109482
  have eq109597 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq109579 X0 x
       have i₂ := eq108502 X0 x
       grind)
    | exact superpose eq108502 eq109579
    | exact resolve eq109579 eq108502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108502 eq109579
  have eq109993 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq109597 (σ x)
       grind)
    | exact superpose eq109597 eq14
    | exact resolve eq14 eq109597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110020 : (σ (M.op x x)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq109993
       have i₂ := eq108499 x
       grind)
    | exact superpose eq108499 eq109993
    | exact resolve eq109993 eq108499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109993
  have eq110051 : (σ y) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq110020
       have i₂ := eq108459
       grind)
    | exact superpose eq108459 eq110020
    | exact resolve eq110020 eq108459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110020
  have eq127358 : ∀ X0 : G, (σ (M.op x y)) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq109578 (σ x) X0
       grind)
    | (have i₁ := eq14
       have i₂ := eq109578 X0 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq109578 eq14
    | (have j1 := eq109578 (σ x) X0
       grind)
    | (have r₁ := eq14
       have r₂ := eq109578 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq109578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109578
  have eq127438 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq127358 X0
       have i₂ := eq108499 x
       grind)
    | exact superpose eq108499 eq127358
    | (have j0 := eq127358 X0
       grind)
    | exact resolve eq127358 eq108499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127358
  have eq127452 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq127438 X0
       have i₂ := eq108459
       grind)
    | exact superpose eq108459 eq127438
    | (have j0 := eq127438 X0
       grind)
    | exact resolve eq127438 eq108459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127438
  have eq127675 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have j0 := eq127452 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127452
  have eq127676 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq127675
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq127675
    | exact resolve eq127675 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127675
  have eq127677 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq127676
       have i₂ := eq8156
       grind)
    | exact superpose eq8156 eq127676
    | exact resolve eq127676 eq8156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8156 eq127676
  have eq127678 : (σ x) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq127677
       have i₂ := eq109597 (σ x)
       grind)
    | exact superpose eq109597 eq127677
    | exact resolve eq127677 eq109597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109597 eq127677
  have eq127769 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq110051
       have i₂ := eq127678
       grind)
    | exact superpose eq127678 eq110051
    | exact resolve eq110051 eq127678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110051
  have eq127875 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op (τ (σ x)) y)) := by
    first
    | (have i₁ := eq109524 (σ x)
       have i₂ := eq127678
       grind)
    | exact superpose eq127678 eq109524
    | (have j0 := eq109524 (σ x)
       grind)
    | (have r₁ := eq109524 (σ x)
       have r₂ := eq127678
       grind)
    | exact resolve eq109524 eq127678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109524 eq127678
  have eq127909 : (σ x) = (σ (M.op (τ (σ x)) y)) := by grind
  clear eq127875
  have eq127928 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq127909
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq127909
    | exact resolve eq127909 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127909
  have eq128013 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq127928
       have i₂ := eq108499 x
       grind)
    | exact superpose eq108499 eq127928
    | exact resolve eq127928 eq108499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108499 eq127928
  have eq128032 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq128013
       have i₂ := eq108459
       grind)
    | exact superpose eq108459 eq128013
    | exact resolve eq128013 eq108459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108459 eq128013
  have eq128037 : False := by grind
  exact eq128037

/-- `Equation312`: `x ◇ x = y ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(m(Y,Y),Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_ppyyy_pyx_Equation312 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) (((Lf 1) ⋆ (Lf 1)) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law312 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (((Lf 1) ⋆ (Lf 1)) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law312.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op (M.op b b) b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op (M.op X1 X1) X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X2
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq26 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X1 X1) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq8 X0 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq8 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 X1
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq41 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) X1) = (k (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X2 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq29
    | exact resolve eq29 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq29 X0 (M.op X1 X1)
       grind)
    | exact superpose eq29 eq8
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25
    | exact resolve eq25 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq19 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq19 eq13
    | (have j1 := eq19 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq163 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq20 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq206 : ∀ X0 X1 X2 : G, (k (τ (M.op X2 X2)) X1) = (τ (k (M.op X0 X0) (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (M.op X2 X2) X1
       have i₂ := eq41 X2 (σ X1) X0
       grind)
    | (have i₁ := eq25 (M.op X2 X2) X1
       have i₂ := eq41 X0 (σ X1) X2
       grind)
    | exact superpose eq41 eq25
    | exact resolve eq25 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq207 : ∀ X0 X1 X2 : G, (k (τ (M.op X0 X0)) X1) = (k (τ (M.op X2 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206 X2 X1 X0
       have i₂ := eq25 (M.op X2 X2) X1
       grind)
    | exact superpose eq25 eq206
    | exact resolve eq206 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq268 : ∀ X0 X1 X2 : G, (k (τ (M.op X0 X0)) (τ X1)) = (τ (k (M.op X2 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X1 (M.op X2 X2)
       have i₂ := eq207 X2 (τ X1) X0
       grind)
    | (have i₁ := eq50 X1 (M.op X2 X2)
       have i₂ := eq207 X0 (τ X1) X2
       grind)
    | exact superpose eq207 eq50
    | exact resolve eq50 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 X1 X2 : G, (τ (k (M.op X0 X0) X1)) = (τ (k (M.op X2 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq268 X0 X1 X2
       have i₂ := eq50 X1 (M.op X0 X0)
       grind)
    | exact superpose eq50 eq268
    | exact resolve eq268 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq268
  have eq479 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X0)) = (τ (k (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq277 X1 X0 x
       have i₂ := eq29 x X0
       grind)
    | exact superpose eq29 eq277
    | exact resolve eq277 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq277
  have eq655 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq31
    | (have j0 := eq31 X0 X1
       grind)
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq705 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq655 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq655
    | (have j0 := eq655 X0 X1
       grind)
    | exact resolve eq655 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq1007 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X1
       have i₂ := eq705 X0 X1
       grind)
    | exact superpose eq705 eq8
    | (have j1 := eq705 X2 X0
       grind)
    | exact resolve eq8 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq1214 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq163 (M.op X0 X0)
       have i₂ := eq46 X0 X0
       grind)
    | exact superpose eq46 eq163
    | (have j0 := eq163 (M.op X0 X0)
       grind)
    | exact resolve eq163 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq163
  have eq1231 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1214 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1490 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ (M.op X0 X0)) X1
       have i₂ := eq1231 X0
       grind)
    | exact superpose eq1231 eq8
    | exact resolve eq8 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231
  have eq1662 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1490 X0 X1
       have i₂ := eq1007 X0 X0 X2
       grind)
    | exact superpose eq1007 eq1490
    | (have j1 := eq1007 (σ X0) X1 X2
       grind)
    | exact resolve eq1490 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007 eq1490
  have eq2646 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq72 x y X0
       grind)
    | exact superpose eq72 eq14
    | (have j1 := eq72 X0 y X0
       grind)
    | exact resolve eq14 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq2761 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq2646 X0
       have j1 := eq1662 y X0 x
       grind)
    | (have r₁ := eq2646 X0
       have r₂ := eq1662 y x x
       grind)
    | exact resolve eq2646 eq1662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662 eq2646
  have eq2787 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = (k (τ (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq207 X0 X1 (σ y)
       have i₂ := eq2761 (σ y)
       grind)
    | exact superpose eq2761 eq207
    | exact resolve eq207 eq2761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq2809 : ∀ X0 : G, (τ (σ y)) = (τ (k (M.op X0 X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq479 (σ y) X0
       have i₂ := eq2761 (M.op (σ y) (σ y))
       grind)
    | exact superpose eq2761 eq479
    | exact resolve eq479 eq2761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq2812 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2761 (σ x)
       grind)
    | exact superpose eq2761 eq14
    | exact resolve eq14 eq2761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2761
  have eq2818 : ∀ X0 : G, (τ (σ y)) = (k (τ (M.op X0 X0)) y) := by
    intro X0
    first
    | (have i₁ := eq2809 X0
       have i₂ := eq25 (M.op X0 X0) y
       grind)
    | exact superpose eq25 eq2809
    | exact resolve eq2809 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2809
  have eq2829 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2787 X0 X1
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2787
    | exact resolve eq2787 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2787
  have eq2835 : ∀ X0 : G, y = (k (τ (M.op X0 X0)) y) := by
    intro X0
    first
    | (have i₁ := eq2818 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2818
    | exact resolve eq2818 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2818
  have eq2845 : y = (k y y) := by
    first
    | (have i₁ := eq2835 x
       have i₂ := eq2829 x y
       grind)
    | exact superpose eq2829 eq2835
    | exact resolve eq2835 eq2829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2829 eq2835
  have eq3096 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq2845
       grind)
    | exact superpose eq2845 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq2845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2845
  have eq3100 : y = (M.op y y) := by grind
  clear eq3096
  have eq3176 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq8 y x
       have i₂ := eq3100
       grind)
    | exact superpose eq3100 eq8
    | exact resolve eq8 eq3100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3100
  have eq3592 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2812
       have i₂ := eq3176 x
       grind)
    | exact superpose eq3176 eq2812
    | exact resolve eq2812 eq3176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2812 eq3176
  have eq3593 : False := by grind
  exact eq3593
