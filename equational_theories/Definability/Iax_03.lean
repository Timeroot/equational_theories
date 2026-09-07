import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation327`: `x ◇ y = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation327 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law327 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law327.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21
    | exact resolve eq21 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq29 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq53 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq71 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq25 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq25
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq98 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X2 X0) = (k X0 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq30 X1 X0 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq30 X0 X0 X2
       grind)
    | exact superpose eq30 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq30 X2 X1 X0
       grind)
    | exact resolve eq12 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X2 (σ X0)) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq30 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 (σ X1) X2 (σ X0)
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq42
  have eq142 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq127 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq127
    | exact resolve eq127 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq186 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 (M.op X1 X2) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq50
    | (have j0 := eq50 (M.op X1 X2) X0
       grind)
    | (have r₁ := eq50 (M.op X0 X0) X0
       have r₂ := eq8 X0 X0 X0
       grind)
    | exact resolve eq50 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq277 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (σ X1) (σ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq8
    | (have j1 := eq32 X1 X0
       grind)
    | exact resolve eq8 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq9
    | (have j1 := eq32 X1 X0
       grind)
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq32 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq142 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq142
    | (have j1 := eq32 X0 X1
       grind)
    | exact resolve eq142 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq325 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq142 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq142 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq142
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq142 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq324 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq324
    | (have j0 := eq324 X0 X1
       grind)
    | exact resolve eq324 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq699 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq302 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq302
    | (have j0 := eq302 (τ X0)
       grind)
    | exact resolve eq302 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq701 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq699 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq699
    | (have j0 := eq699 X0
       grind)
    | exact resolve eq699 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq704 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq701 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq701
    | (have j0 := eq701 X0
       grind)
    | exact resolve eq701 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq714 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq704 (τ X0)
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq704
    | (have j0 := eq704 (τ X0)
       grind)
    | exact resolve eq704 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq726 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq37
    | exact resolve eq37 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq10
    | (have j1 := eq37 X1 X0
       grind)
    | exact resolve eq10 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq808 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq726 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq726
    | (have j0 := eq726 X0 X1
       grind)
    | exact resolve eq726 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq873 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  clear eq808
  have eq2259 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq71
    | (have j0 := eq71 X1 (σ X0)
       grind)
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq2336 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2259 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2259
    | (have j0 := eq2259 X0 X1
       grind)
    | exact resolve eq2259 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259
  have eq2825 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq302 X0
       have i₂ := eq2336 X0 X0
       grind)
    | exact superpose eq2336 eq302
    | (have j0 := eq302 X0
       have j1 := eq2336 X0 X0
       grind)
    | (have r₁ := eq302 x
       have r₂ := eq2336 x x
       grind)
    | exact resolve eq302 eq2336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336
  have eq2852 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2825 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2825
  have eq3115 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq284 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq284
    | exact resolve eq284 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3181 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3115 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3115
    | (have j0 := eq3115 X0 X1
       grind)
    | exact resolve eq3115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3115
  have eq3806 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq3807 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3806 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3806
  have eq4352 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq119 x y X0
       grind)
    | exact superpose eq119 eq14
    | (have j1 := eq119 y x X0
       grind)
    | exact resolve eq14 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4470 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq119 X0 X1 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq6263 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3181 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3181
    | (have j0 := eq3181 X1 (τ X0)
       grind)
    | exact resolve eq3181 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3181
  have eq8305 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (τ X0) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq325 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq325
    | (have j0 := eq325 X1 (τ X0)
       grind)
    | exact resolve eq325 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq8419 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8305 X0 X1
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq8305
    | (have j0 := eq8305 X0 X1
       grind)
    | exact resolve eq8305 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq8305
  have eq9607 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq349 x y
       grind)
    | exact superpose eq349 eq14
    | (have j1 := eq349 x y
       grind)
    | exact resolve eq14 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9677 : y = (k y x) := by
    first
    | (have j1 := eq873 x y
       grind)
    | (have r₁ := eq9607
       have r₂ := eq873 x y
       grind)
    | exact resolve eq9607 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9607
  have eq10071 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq30 x X0 y
       have i₂ := eq9677
       grind)
    | exact superpose eq9677 eq30
    | (have j0 := eq30 x X0 y
       grind)
    | exact resolve eq30 eq9677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq9677
  have eq11597 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 y) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 x y
       have i₂ := eq10071 X1
       grind)
    | exact superpose eq10071 eq8
    | (have j1 := eq10071 X0
       grind)
    | exact resolve eq8 eq10071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10071
  have eq16952 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq11597 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11597
  have eq16953 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq16952 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16952
  have eq17717 : y = (k y (M.op y x)) := by grind
  have eq17720 : ∀ X0 : G, (τ X0) = (τ (M.op y x)) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq6263 X0 y
       have i₂ := eq16953 y
       grind)
    | exact superpose eq16953 eq6263
    | (have j0 := eq6263 X0 y
       grind)
    | exact resolve eq6263 eq16953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6263
  have eq17789 : ∀ X0 : G, (k y X0) = (M.op X0 x) ∨ (τ X0) = (τ (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq17720 X0
       have i₂ := eq16953 X0
       grind)
    | exact superpose eq16953 eq17720
    | (have j0 := eq17720 X0
       grind)
    | exact resolve eq17720 eq16953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17720
  have eq18570 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op y x))) ∨ (M.op (σ y) (σ y)) = (σ (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq277 y (M.op y x) X0
       have i₂ := eq17717
       grind)
    | exact superpose eq17717 eq277
    | (have j0 := eq277 y (M.op y x) x
       grind)
    | exact resolve eq277 eq17717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277 eq17717
  have eq33936 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq186 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq33990 : (M.op y x) = (k (M.op y x) y) := by
    first
    | (have i₁ := eq33936 y
       have i₂ := eq16953 y
       grind)
    | exact superpose eq16953 eq33936
    | exact resolve eq33936 eq16953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34085 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq24 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq33936 (σ X0)
       grind)
    | exact superpose eq33936 eq24
    | exact resolve eq24 eq33936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq33936
  have eq34581 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq758 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq34582 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq34581 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34581
    | (have j0 := eq34581 X0
       grind)
    | exact resolve eq34581 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34581
  have eq37093 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq34582 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq34582
    | (have j0 := eq34582 (σ X0)
       grind)
    | exact resolve eq34582 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34582
  have eq37111 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37093 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq37093
    | (have j0 := eq37093 X0
       grind)
    | exact resolve eq37093 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37093
  have eq45894 : ∀ X0 : G, (σ (τ X0)) = (M.op y x) ∨ (k y X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y x)
       have i₂ := eq17789 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq17789 X0
       grind)
    | exact superpose eq17789 eq10
    | (have j1 := eq17789 X0
       grind)
    | exact resolve eq10 eq17789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17789
  have eq45931 : ∀ X0 : G, (k y X0) = (M.op X0 x) ∨ (M.op y x) = X0 := by
    intro X0
    first
    | (have i₁ := eq45894 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45894
    | (have j0 := eq45894 X0
       grind)
    | exact resolve eq45894 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45894
  have eq49941 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq4352 X0
       have i₂ := eq3807 y x
       grind)
    | exact superpose eq3807 eq4352
    | (have j0 := eq4352 X0
       have j1 := eq3807 y x
       grind)
    | exact resolve eq4352 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3807 eq4352
  have eq49955 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq49941 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49941
  have eq50194 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq49955 (σ x)
       grind)
    | exact superpose eq49955 eq14
    | exact resolve eq14 eq49955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49955
  have eq50221 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq50194
       have i₂ := eq16953 x
       grind)
    | exact superpose eq16953 eq50194
    | exact resolve eq50194 eq16953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50194
  have eq50578 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq714 X0
       have i₂ := eq8419 X0 X0
       grind)
    | exact superpose eq8419 eq714
    | (have j0 := eq714 X0
       have j1 := eq8419 X0 X0
       grind)
    | (have r₁ := eq714 x
       have r₂ := eq8419 x x
       grind)
    | exact resolve eq714 eq8419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq8419
  have eq50587 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq50578 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50578
  have eq57019 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34085 X0
       have i₂ := eq284 X0 X1
       grind)
    | (have i₁ := eq34085 X0
       have i₂ := eq284 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq284 eq34085
    | (have j1 := eq284 X1 X0
       grind)
    | exact resolve eq34085 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq34085
  have eq57437 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq50221
       have i₂ := eq349 x x
       grind)
    | exact superpose eq349 eq50221
    | (have j1 := eq349 x x
       grind)
    | exact resolve eq50221 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq57446 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq873 x x
       grind)
    | (have r₁ := eq57437
       have r₂ := eq873 x x
       grind)
    | exact resolve eq57437 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57437
  have eq57502 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq302 x
       have i₂ := eq57446
       grind)
    | exact superpose eq57446 eq302
    | (have j0 := eq302 x
       grind)
    | exact resolve eq302 eq57446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57516 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq37111 x
       have i₂ := eq57446
       grind)
    | exact superpose eq57446 eq37111
    | (have j0 := eq37111 x
       grind)
    | exact resolve eq37111 eq57446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57446
  have eq57545 : (σ x) = (σ (M.op x x)) ∨ x = (M.op y x) := by grind
  clear eq57516
  have eq57553 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq57502
  have eq59120 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq50221
       have i₂ := eq57553
       grind)
    | exact superpose eq57553 eq50221
    | exact resolve eq50221 eq57553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50221 eq57553
  have eq59189 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op y x) := by grind
  clear eq59120
  have eq59212 : x = (M.op y x) := by
    first
    | (have r₁ := eq59189
       have r₂ := eq57545
       grind)
    | exact resolve eq59189 eq57545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57545 eq59189
  have eq62302 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50587 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq50587
    | (have j0 := eq50587 (σ X0)
       grind)
    | exact resolve eq50587 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50587
  have eq62408 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62302 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq62302
    | (have j0 := eq62302 X0
       grind)
    | exact resolve eq62302 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62302
  have eq63415 : (M.op (σ y) (σ y)) ≠ (σ (M.op y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op y x))) := by
    first
    | (have i₁ := eq4470 y (M.op y x)
       have i₂ := eq33990
       grind)
    | exact superpose eq33990 eq4470
    | (have j0 := eq4470 y (M.op y x)
       grind)
    | exact resolve eq4470 eq33990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4470 eq33990
  have eq63418 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op y x))) := by
    first
    | (have j1 := eq18570 (σ y)
       grind)
    | (have r₁ := eq63415
       have r₂ := eq18570 x
       grind)
    | exact resolve eq63415 eq18570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18570 eq63415
  have eq63421 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq63418
       have i₂ := eq59212
       grind)
    | exact superpose eq59212 eq63418
    | exact resolve eq63418 eq59212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63418
  have eq63447 : y = (k y (τ (M.op (σ y) (σ x)))) := by
    first
    | (have i₁ := eq142 y
       have i₂ := eq63421
       grind)
    | exact superpose eq63421 eq142
    | exact resolve eq142 eq63421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq63452 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op y y) = (k y y) := by
    first
    | (have i₁ := eq2852 y
       have i₂ := eq63421
       grind)
    | exact superpose eq63421 eq2852
    | (have j0 := eq2852 y
       grind)
    | exact resolve eq2852 eq63421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852
  have eq63522 : (M.op y x) = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq63452
       have i₂ := eq16953 y
       grind)
    | exact superpose eq16953 eq63452
    | exact resolve eq63452 eq16953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63452
  have eq63529 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq63522
       have i₂ := eq59212
       grind)
    | exact superpose eq59212 eq63522
    | exact resolve eq63522 eq59212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63522
  have eq64302 : y = (k y (τ (σ y))) ∨ x = (k y y) := by
    first
    | (have i₁ := eq63447
       have i₂ := eq63529
       grind)
    | exact superpose eq63529 eq63447
    | exact resolve eq63447 eq63529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63447 eq63529
  have eq64374 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq64302
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq64302
    | exact resolve eq64302 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64302
  have eq64445 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq45931 y
       have i₂ := eq64374
       grind)
    | exact superpose eq64374 eq45931
    | (have j0 := eq45931 y
       grind)
    | exact resolve eq45931 eq64374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45931
  have eq64502 : x ≠ y ∨ x = (k y y) := by grind
  clear eq64374
  have eq64518 : y = (M.op y x) ∨ x = (k y y) := by grind
  clear eq64445
  have eq64547 : x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq64518
       have i₂ := eq59212
       grind)
    | exact superpose eq59212 eq64518
    | exact resolve eq64518 eq59212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64518
  have eq64573 : x = (k y y) := by
    first
    | (have r₁ := eq64547
       have r₂ := eq64502
       grind)
    | exact resolve eq64547 eq64502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64502 eq64547
  have eq64685 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq302 y
       have i₂ := eq64573
       grind)
    | exact superpose eq64573 eq302
    | (have j0 := eq302 y
       grind)
    | exact resolve eq302 eq64573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64795 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq64685
       have i₂ := eq63421
       grind)
    | exact superpose eq63421 eq64685
    | exact resolve eq64685 eq63421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64685
  have eq66255 : (M.op (σ y) (σ x)) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq63421
       have i₂ := eq62408 y
       grind)
    | exact superpose eq62408 eq63421
    | (have j1 := eq62408 y
       grind)
    | exact resolve eq63421 eq62408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62408 eq63421
  have eq66308 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq66255
       have i₂ := eq64573
       grind)
    | exact superpose eq64573 eq66255
    | exact resolve eq66255 eq64573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64573 eq66255
  have eq66325 : y = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq66308
       have i₂ := eq16953 y
       grind)
    | exact superpose eq16953 eq66308
    | exact resolve eq66308 eq16953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66308
  have eq66333 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq66325
       have i₂ := eq59212
       grind)
    | exact superpose eq59212 eq66325
    | exact resolve eq66325 eq59212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66325
  have eq66395 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ y) (σ x)
       have i₂ := eq66333
       grind)
    | exact superpose eq66333 eq8
    | exact resolve eq8 eq66333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66333
  have eq66624 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq66395 (σ x)
       grind)
    | exact superpose eq66395 eq14
    | exact resolve eq14 eq66395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66395
  have eq66653 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq66624
       have i₂ := eq16953 x
       grind)
    | exact superpose eq16953 eq66624
    | exact resolve eq66624 eq16953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16953 eq66624
  have eq66812 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq66653
       have i₂ := eq57019 x x
       grind)
    | exact superpose eq57019 eq66653
    | (have j1 := eq57019 x x
       grind)
    | exact resolve eq66653 eq57019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57019
  have eq66825 : x = (k x x) ∨ x = y := by
    first
    | (have j1 := eq873 x x
       grind)
    | (have r₁ := eq66812
       have r₂ := eq873 x x
       grind)
    | exact resolve eq66812 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq66812
  have eq67021 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq302 x
       have i₂ := eq66825
       grind)
    | exact superpose eq66825 eq302
    | (have j0 := eq302 x
       grind)
    | exact resolve eq302 eq66825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq67043 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq37111 x
       have i₂ := eq66825
       grind)
    | exact superpose eq66825 eq37111
    | (have j0 := eq37111 x
       grind)
    | exact resolve eq37111 eq66825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37111 eq66825
  have eq67077 : (σ x) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq67043
  have eq67087 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq67021
  have eq68125 : (σ x) ≠ (σ (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq66653
       have i₂ := eq67087
       grind)
    | exact superpose eq67087 eq66653
    | exact resolve eq66653 eq67087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66653 eq67087
  have eq68239 : (σ x) ≠ (σ (M.op x x)) ∨ x = y := by grind
  clear eq68125
  have eq68268 : x = y := by
    first
    | (have r₁ := eq68239
       have r₂ := eq67077
       grind)
    | exact resolve eq68239 eq67077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67077 eq68239
  have eq68299 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq68268
       grind)
    | exact superpose eq68268 eq14
    | exact resolve eq14 eq68268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68345 : x = (M.op x x) := by
    first
    | (have i₁ := eq59212
       have i₂ := eq68268
       grind)
    | exact superpose eq68268 eq59212
    | exact resolve eq59212 eq68268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59212
  have eq68374 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq64795
       have i₂ := eq68268
       grind)
    | exact superpose eq68268 eq64795
    | exact resolve eq64795 eq68268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64795 eq68268
  have eq68376 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq68374
  have eq68404 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq68299
       have i₂ := eq68345
       grind)
    | exact superpose eq68345 eq68299
    | exact resolve eq68299 eq68345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68299 eq68345
  have eq68406 : False := by grind
  exact eq68406

/-- `Equation329`: `x ◇ y = x ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_pyy_pxx_pyx_Equation329 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law329 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law329.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq24
    | exact resolve eq24 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq27 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X2 X1) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X1 X0
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
  have eq35 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X0 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq41 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 X0 X1
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq42 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 X0 X1 X2
       have i₂ := eq8 X2 X1 X0
       grind)
    | exact superpose eq8 eq35
    | (have j0 := eq35 X0 X1 X2
       grind)
    | exact resolve eq35 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq48 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq21 (τ X0)
       grind)
    | exact superpose eq21 eq17
    | exact resolve eq17 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq17
  have eq53 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48
    | exact resolve eq48 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq53
    | exact resolve eq53 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq53
  have eq72 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ X0) (σ X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq8
    | exact resolve eq8 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
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
  have eq94 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq40 (τ X0) X1
       grind)
    | exact superpose eq40 eq18
    | (have j1 := eq40 (τ X0) X1
       grind)
    | exact resolve eq18 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq104 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq109 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq52
    | exact resolve eq52 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq148 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq42 X0 (σ y) (σ x)
       grind)
    | (have i₁ := eq14
       have i₂ := eq42 (σ y) x (σ x)
       grind)
    | exact superpose eq42 eq14
    | (have j1 := eq42 X0 (σ y) x
       grind)
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (τ X0) (τ X0))
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
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
  have eq439 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (σ X0) (σ X1)
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq8
    | (have j1 := eq41 X1 X0
       grind)
    | exact resolve eq8 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (k (M.op X2 (σ X0)) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 (σ X0) (σ X1) X2
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq27
    | (have j1 := eq41 X1 X0
       grind)
    | exact resolve eq27 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq455 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq457 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (k (M.op X2 (σ X0)) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq444 X0 X1 X2
       have i₂ := eq25 X1
       grind)
    | exact superpose eq25 eq444
    | (have j0 := eq444 X0 X1 X2
       grind)
    | exact resolve eq444 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq484 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (k (M.op X2 (σ X0)) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq457 X0 X1 X2
       have j1 := eq455 X1 X0
       grind)
    | (have r₁ := eq457 X1 X0 X2
       have r₂ := eq455 X0 X1
       grind)
    | exact resolve eq457 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq457
  have eq524 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (τ X0) (τ X0)
       have i₂ := eq177 X0
       grind)
    | exact superpose eq177 eq8
    | exact resolve eq8 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq4016 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq94
    | exact resolve eq94 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq4205 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4016 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq4016
    | (have j0 := eq4016 X0 X1
       grind)
    | exact resolve eq4016 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4016
  have eq4440 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq148 (σ x)
       have i₂ := eq25 x
       grind)
    | exact superpose eq25 eq148
    | (have j0 := eq148 (σ x)
       grind)
    | exact resolve eq148 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq4459 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq4440
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq4440
    | exact resolve eq4440 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4440
  have eq7664 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0)
       have i₂ := eq104 X0 X1
       grind)
    | exact superpose eq104 eq9
    | (have j1 := eq104 X0 X1
       grind)
    | exact resolve eq9 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq7828 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7664 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq7664
    | (have j0 := eq7664 X0 X1
       grind)
    | exact resolve eq7664 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7664
  have eq9348 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq437
       have i₂ := eq42 x y X0
       grind)
    | exact superpose eq42 eq437
    | (have j1 := eq42 x y X0
       grind)
    | exact resolve eq437 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq437
  have eq9349 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq9348 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9348
  have eq28487 : ∀ X0 X1 X2 : G, (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq439 (τ X0) (τ X1) X2
       have i₂ := eq109 X1 X0
       grind)
    | exact superpose eq109 eq439
    | (have j0 := eq439 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq439 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq29131 : ∀ X0 X1 X2 : G, (M.op X2 (k X0 X1)) = (M.op X2 (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28487 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq28487
    | (have j0 := eq28487 X0 X1 X2
       grind)
    | exact resolve eq28487 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28487
  have eq29197 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (k X0 X1)) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29131 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29131
    | (have j0 := eq29131 X0 X1 X2
       grind)
    | exact resolve eq29131 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29131
  have eq29221 : ∀ X0 X1 X2 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29197 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29197
    | (have j0 := eq29197 X0 X1 X2
       grind)
    | exact resolve eq29197 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29197
  have eq29227 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29221 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq29221
    | (have j0 := eq29221 X0 X1 X2
       grind)
    | exact resolve eq29221 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29221
  have eq29230 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29227 X0 X1 X2
       have i₂ := eq54 X1
       grind)
    | exact superpose eq54 eq29227
    | (have j0 := eq29227 X0 X1 X2
       grind)
    | exact resolve eq29227 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29227
  have eq29911 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k X1 (τ X0))) = (k (M.op X2 (σ X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq484 X0 (τ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq484
    | exact resolve eq484 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq30439 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 (τ X0))) = (k (M.op X2 (σ X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29911 X0 X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq29911
    | (have j0 := eq29911 X0 X1 X2
       grind)
    | exact resolve eq29911 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq29911
  have eq30589 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (k (M.op X2 (σ X1)) X0) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30439 X0 X1 X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq30439
    | (have j0 := eq30439 X0 X1 X2
       grind)
    | exact resolve eq30439 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq30439
  have eq47441 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X1) = (M.op X2 (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq29230 X1 X0 X2
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq29230 X0 X1 X2
       grind)
    | exact superpose eq29230 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq29230 X1 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq29230 X0 X1 X2
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq29230 X0 X0 X2
       grind)
    | (have r₁ := eq11 X0 (k X0 X1)
       have r₂ := eq29230 X0 X1 (k X0 X1)
       grind)
    | exact resolve eq11 eq29230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29230
  have eq47940 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X1) = (M.op X2 (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq47441 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47441
  have eq55815 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X2 (k X0 X1)) ∨ (M.op X3 X0) = (M.op X3 (k X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X0 X0
       have i₂ := eq47940 X1 X0 X3
       grind)
    | exact superpose eq47940 eq8
    | (have j1 := eq47940 X1 X0 X2
       grind)
    | exact resolve eq8 eq47940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47940
  have eq61226 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq7828 y x
       grind)
    | exact superpose eq7828 eq14
    | (have j1 := eq7828 y x
       grind)
    | exact resolve eq14 eq7828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7828
  have eq61268 : (k y x) = (M.op y y) := by
    first
    | (have j1 := eq4205 x y
       grind)
    | (have r₁ := eq61226
       have r₂ := eq4205 x y
       grind)
    | exact resolve eq61226 eq4205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4205 eq61226
  have eq70624 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x x))) ∨ (M.op X1 y) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (σ y) (σ x)
       have i₂ := eq9349 X1
       grind)
    | exact superpose eq9349 eq8
    | (have j1 := eq9349 X1
       grind)
    | exact resolve eq8 eq9349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9349
  have eq70648 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op X1 y) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq70624 X0 X1
       have i₂ := eq72 x X0
       grind)
    | exact superpose eq72 eq70624
    | (have j0 := eq70624 X0 X1
       grind)
    | exact resolve eq70624 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70624
  have eq72609 : ∀ X0 X1 : G, (M.op X0 (τ (σ y))) = (M.op X0 (τ (M.op (σ y) (σ x)))) ∨ (M.op X1 y) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq524 (σ y) X0
       have i₂ := eq70648 (σ y) X1
       grind)
    | exact superpose eq70648 eq524
    | (have j1 := eq70648 X0 X1
       grind)
    | exact resolve eq524 eq70648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524 eq70648
  have eq72653 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (τ (M.op (σ y) (σ x)))) ∨ (M.op X1 y) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq72609 X0 X1
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq72609
    | (have j0 := eq72609 X0 X1
       grind)
    | exact resolve eq72609 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72609
  have eq129070 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (k (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30589 X0 (τ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30589
    | exact resolve eq30589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129189 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 X0) ∨ (k X1 X0) = (k (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X0 X0
       have i₂ := eq129070 X1 X0 X3
       grind)
    | (have i₁ := eq8 X0 X0 X1
       have i₂ := eq129070 X0 X1 X2
       grind)
    | exact superpose eq129070 eq8
    | (have j1 := eq129070 X1 X0 X3
       grind)
    | exact resolve eq8 eq129070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129070
  have eq129254 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (k X1 X0) = (k (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq129189 X0 X1 X2 X3
       have i₂ := eq8 X2 X1 X0
       grind)
    | exact superpose eq8 eq129189
    | (have j0 := eq129189 X0 X1 X2 X3
       grind)
    | exact resolve eq129189 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129189
  have eq135356 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq55815 X1 X2 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55815
  have eq135357 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq135356 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135356
  have eq135666 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135357 X2 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq135357
    | exact resolve eq135357 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135679 : ∀ X0 X1 X2 : G, (M.op X2 (τ X0)) = (M.op X2 (τ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135357 X2 (τ X0) (τ X1)
       have i₂ := eq109 X1 X0
       grind)
    | exact superpose eq109 eq135357
    | exact resolve eq135357 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq135357
  have eq136480 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (σ (k X0 X1))) = (M.op X2 (σ (M.op X3 X0))) ∨ (M.op X4 X1) = (M.op X4 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq135666 (M.op X3 X0) X1 X2
       have i₂ := eq129254 X1 X0 X4 X3
       grind)
    | exact superpose eq129254 eq135666
    | (have j1 := eq129254 (σ (M.op X3 X0)) (σ (k X0 X1)) X2 X3
       grind)
    | exact resolve eq135666 eq129254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129254
  have eq136836 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (M.op X3 X0))) ∨ (M.op X4 X1) = (M.op X4 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq136480 X0 X1 X2 X3 X4
       have i₂ := eq135666 X0 X1 X2
       grind)
    | exact superpose eq135666 eq136480
    | (have j0 := eq136480 (σ (M.op X3 X0)) (σ X0) X2 X3 X2
       grind)
    | exact resolve eq136480 eq135666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135666 eq136480
  have eq137113 : ∀ X0 X1 X2 X3 : G, (M.op X2 (τ (k (σ X0) X1))) = (M.op X2 (τ (M.op X3 (σ X0)))) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq135679 (M.op X3 (σ X0)) X1 X2
       have i₂ := eq30589 X1 X0 X3
       grind)
    | exact superpose eq30589 eq135679
    | (have j1 := eq30589 X1 X0 X2
       grind)
    | exact resolve eq135679 eq30589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30589
  have eq137395 : ∀ X0 X1 X2 X3 : G, (M.op X2 (τ (σ X0))) = (M.op X2 (τ (M.op X3 (σ X0)))) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq137113 X0 X1 X2 X3
       have i₂ := eq135679 (σ X0) X1 X2
       grind)
    | exact superpose eq135679 eq137113
    | (have j0 := eq137113 X0 X1 X2 X3
       grind)
    | exact resolve eq137113 eq135679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135679 eq137113
  have eq137444 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X2 (τ (M.op X3 (σ X0)))) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq137395 X0 X1 X2 X3
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq137395
    | (have j0 := eq137395 X0 X1 X2 X3
       grind)
    | exact resolve eq137395 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137395
  have eq170687 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 (σ X2)) ∨ (M.op X3 X2) = (M.op X3 (τ (M.op X4 (σ X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X1 (σ X2) X0
       have i₂ := eq137444 X2 X0 X3 X4
       grind)
    | (have i₁ := eq8 X0 X1 X1
       have i₂ := eq137444 X0 X1 X2 X3
       grind)
    | exact superpose eq137444 eq8
    | (have j1 := eq137444 X2 X1 X3 X4
       grind)
    | exact resolve eq8 eq137444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137444
  have eq170689 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op X1 (σ X2)) ∨ (M.op X3 X2) = (M.op X3 (τ (M.op X4 (σ X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq170687 X0 X1 X2 X3 X4
       have i₂ := eq8 X1 X0 X0
       grind)
    | exact superpose eq8 eq170687
    | (have j0 := eq170687 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq170687 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170687
  have eq173454 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 (σ X2)) ∨ (M.op X0 X2) = (M.op X0 (τ (M.op X1 (σ X2)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq170689 X0 X1 X2 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173455 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (τ (M.op X1 (σ X2)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq173454 X0 X1 X2
       have j1 := eq170689 X0 X1 X2 X0 X1
       grind)
    | (have r₁ := eq173454 X1 X1 X2
       have r₂ := eq170689 X2 X1 X2 x x
       grind)
    | (have r₁ := eq173454 X1 X1 (σ X2)
       have r₂ := eq170689 (σ (σ X2)) X1 X2 x x
       grind)
    | exact resolve eq173454 eq170689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170689 eq173454
  have eq173746 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 y) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq72653 X0 X1
       have i₂ := eq173455 X0 (σ y) x
       grind)
    | exact superpose eq173455 eq72653
    | (have j0 := eq72653 X0 X0
       grind)
    | exact resolve eq72653 eq173455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72653 eq173455
  have eq175081 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq173746 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173746
  have eq175082 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq175081 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175081
  have eq175195 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq72 y X0
       have i₂ := eq175082 y
       grind)
    | exact superpose eq175082 eq72
    | exact resolve eq72 eq175082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq175893 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq4459
       have i₂ := eq175082 x
       grind)
    | exact superpose eq175082 eq4459
    | exact resolve eq4459 eq175082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4459
  have eq175950 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq175893
  have eq175964 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq175950
       have i₂ := eq61268
       grind)
    | exact superpose eq61268 eq175950
    | exact resolve eq175950 eq61268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61268 eq175950
  have eq176408 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq175964
       have i₂ := eq175082 y
       grind)
    | exact superpose eq175082 eq175964
    | exact resolve eq175964 eq175082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175964
  have eq179847 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq176408
       grind)
    | exact superpose eq176408 eq14
    | exact resolve eq14 eq176408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180198 : (σ (M.op x x)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq179847
       have i₂ := eq175082 x
       grind)
    | exact superpose eq175082 eq179847
    | exact resolve eq179847 eq175082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179847
  have eq181279 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op X1 X2) = (M.op X1 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq136836 x X2 X0 y X1
       have i₂ := eq175195 X0
       grind)
    | exact superpose eq175195 eq136836
    | (have j0 := eq136836 (σ x) (σ y) X2 x X0
       grind)
    | exact resolve eq136836 eq175195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136836 eq175195
  have eq193068 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (σ (M.op y x)) ∨ (M.op X0 X1) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq176408
       have i₂ := eq181279 (σ x) X0 X1
       grind)
    | exact superpose eq181279 eq176408
    | (have j1 := eq181279 X0 X0 X1
       grind)
    | exact resolve eq176408 eq181279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176408 eq181279
  have eq193224 : ∀ X0 X1 : G, (σ (M.op x x)) = (σ (M.op y x)) ∨ (M.op X0 X1) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq193068 X0 X1
       have i₂ := eq25 x
       grind)
    | exact superpose eq25 eq193068
    | (have j0 := eq193068 X0 X1
       grind)
    | exact resolve eq193068 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193068
  have eq193236 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have j0 := eq193224 X0 X1
       grind)
    | (have r₁ := eq193224 X0 X1
       have r₂ := eq180198
       grind)
    | exact resolve eq193224 eq180198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180198 eq193224
  have eq195565 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq193236 (σ X0) (σ X0)
       grind)
    | exact superpose eq193236 eq25
    | exact resolve eq25 eq193236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq195626 : (σ (M.op x y)) ≠ (M.op (σ x) x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq193236 (σ x) (σ y)
       grind)
    | exact superpose eq193236 eq14
    | exact resolve eq14 eq193236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193236
  have eq197085 : (σ (M.op x x)) ≠ (M.op (σ x) x) := by
    first
    | (have i₁ := eq195626
       have i₂ := eq175082 x
       grind)
    | exact superpose eq175082 eq195626
    | exact resolve eq195626 eq175082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175082 eq195626
  have eq197812 : False := by grind
  exact eq197812

/-- `Equation333`: `x ◇ y = y ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation333 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law333 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law333.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) := by
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
  have eq16 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X1)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq17
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
       have i₂ := eq12 X0 (M.op X0 X1)
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
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  clear eq16
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23
    | exact resolve eq23 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
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
  have eq59 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq27 (τ X1) X0
       grind)
    | exact superpose eq27 eq18
    | (have j1 := eq27 (τ X1) X0
       grind)
    | exact resolve eq18 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq93 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq37
  have eq108 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq93 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq93
    | exact resolve eq93 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq147 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
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
  have eq159 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq164 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) (σ X1)
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X0 X1
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq216 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq45 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq45
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq41 (σ X1) X0
       grind)
    | exact superpose eq41 eq23
    | (have j1 := eq41 (σ X1) X1
       grind)
    | exact resolve eq23 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq791 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
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
  clear eq32
  have eq863 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq791 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq791
    | (have j0 := eq791 X0 X1
       grind)
    | exact resolve eq791 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq951 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq59
    | exact resolve eq59 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq994 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq951 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq951
    | (have j0 := eq951 X0 X1
       grind)
    | exact resolve eq951 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq1415 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) (σ X1)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq8
    | (have j1 := eq56 X0 X1
       grind)
    | exact resolve eq8 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1805 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq159
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq159
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq159 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1806 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq159
       have i₂ := eq41 y x
       grind)
    | exact superpose eq41 eq159
    | (have j1 := eq41 y x
       grind)
    | exact resolve eq159 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq1807 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq159
       have i₂ := eq994 y x
       grind)
    | exact superpose eq994 eq159
    | (have j1 := eq994 y x
       grind)
    | (have r₁ := eq159
       have r₂ := eq994 y x
       grind)
    | exact resolve eq159 eq994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq1808 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq159
       have i₂ := eq863 y x
       grind)
    | exact superpose eq863 eq159
    | (have j1 := eq863 (σ y) (σ x)
       grind)
    | (have r₁ := eq159
       have r₂ := eq863 y x
       grind)
    | exact resolve eq159 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq863
  have eq1809 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1808
  have eq1810 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq1807
  have eq1811 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq1806
  have eq1812 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1805
  have eq1832 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45 (σ x) (σ x)
       have i₂ := eq1811
       grind)
    | exact superpose eq1811 eq45
    | exact resolve eq45 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1811
  have eq1838 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1832
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq1832
    | exact resolve eq1832 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1832
  have eq1991 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq2339 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq147 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq147
    | (have j0 := eq147 X1 (τ X0)
       grind)
    | exact resolve eq147 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq2457 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2339 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2339
    | (have j0 := eq2339 X0 X1
       grind)
    | exact resolve eq2339 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2339
  have eq2475 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2457 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2457
    | (have j0 := eq2457 X0 X1
       grind)
    | exact resolve eq2457 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457
  have eq2498 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq1838
       grind)
    | exact superpose eq1838 eq9
    | exact resolve eq9 eq1838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838
  have eq2546 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2498
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2498
    | exact resolve eq2498 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2498
  have eq2547 : y = (k y y) := by
    first
    | (have j1 := eq62 y y
       grind)
    | (have r₁ := eq2546
       have r₂ := eq62 y y
       grind)
    | exact resolve eq2546 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq2546
  have eq2809 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq164 y y
       have i₂ := eq2547
       grind)
    | exact superpose eq2547 eq164
    | (have j0 := eq164 y y
       grind)
    | exact resolve eq164 eq2547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq2547
  have eq2811 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq2809
  have eq4696 : x = (k x (τ (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq108 x
       have i₂ := eq1812
       grind)
    | exact superpose eq1812 eq108
    | exact resolve eq108 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4703 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq4704 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (σ x) (σ x)
       have i₂ := eq1812
       grind)
    | exact superpose eq1812 eq8
    | exact resolve eq8 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4714 : (σ x) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4703
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq4703
    | exact resolve eq4703 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4703
  have eq4717 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4696
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4696
    | exact resolve eq4696 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4696
  have eq5080 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq4717
       grind)
    | exact superpose eq4717 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq4717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5085 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5080
  have eq5583 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq5085
  have eq7182 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4714
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq4714
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq4714 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4714
  have eq7247 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq7182
  have eq8534 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq108 x
       have i₂ := eq1809
       grind)
    | exact superpose eq1809 eq108
    | exact resolve eq108 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8544 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 (σ x) (σ x)
       have i₂ := eq1809
       grind)
    | exact superpose eq1809 eq8
    | exact resolve eq8 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809
  have eq8558 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8534
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq8534
    | exact resolve eq8534 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8534
  have eq9039 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq8558
       grind)
    | exact superpose eq8558 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq8558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8558
  have eq9048 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq9039
  have eq11901 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq108 x
       have i₂ := eq1810
       grind)
    | exact superpose eq1810 eq108
    | exact resolve eq108 eq1810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1810
  have eq11930 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11901
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq11901
    | exact resolve eq11901 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11901
  have eq11931 : x = (k x y) := by grind
  clear eq11930
  have eq11969 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1991 (τ X0) (τ X1)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq1991
    | (have j0 := eq1991 (τ X0) (τ X1)
       grind)
    | exact resolve eq1991 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq12030 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11969 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq11969
    | (have j0 := eq11969 X0 X1
       grind)
    | exact resolve eq11969 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11969
  have eq12041 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12030 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq12030
    | (have j0 := eq12030 X0 X1
       grind)
    | exact resolve eq12030 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12030
  have eq12046 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12041 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12041
    | (have j0 := eq12041 X0 X1
       grind)
    | exact resolve eq12041 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12041
  have eq12047 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12046 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12046
    | (have j0 := eq12046 X0 X1
       grind)
    | exact resolve eq12046 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12046
  have eq12063 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1991 x y
       have i₂ := eq11931
       grind)
    | exact superpose eq11931 eq1991
    | (have j0 := eq1991 x y
       grind)
    | exact resolve eq1991 eq11931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991
  have eq12346 : x ≠ y ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12047 x y
       have i₂ := eq4717
       grind)
    | exact superpose eq4717 eq12047
    | (have j0 := eq12047 x y
       grind)
    | exact resolve eq12047 eq4717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4717 eq12047
  have eq12355 : x ≠ y ∨ y = (M.op x y) := by grind
  clear eq12346
  have eq12465 : x = (M.op x y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq11931
       have i₂ := eq2475 x y
       grind)
    | exact superpose eq2475 eq11931
    | (have j1 := eq2475 x y
       grind)
    | exact resolve eq11931 eq2475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2475 eq11931
  have eq12586 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12465
       have r₂ := eq5583
       grind)
    | exact resolve eq12465 eq5583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5583 eq12465
  have eq15105 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4704
       grind)
    | exact superpose eq4704 eq14
    | exact resolve eq14 eq4704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4704
  have eq15510 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15105
       have i₂ := eq7247
       grind)
    | exact superpose eq7247 eq15105
    | exact resolve eq15105 eq7247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7247 eq15105
  have eq15512 : (σ x) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq15510
  have eq16961 : (τ (σ y)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq280 (σ x) x
       have i₂ := eq1812
       grind)
    | exact superpose eq1812 eq280
    | exact resolve eq280 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq1812
  have eq17170 : (τ (σ y)) = (k (τ (σ x)) x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16961
       have r₂ := eq15512
       grind)
    | exact resolve eq16961 eq15512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15512 eq16961
  have eq17205 : (k x x) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17170
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq17170
    | exact resolve eq17170 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17170
  have eq17214 : y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17205
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq17205
    | exact resolve eq17205 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17205
  have eq17252 : y = (M.op x x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq216 x x
       have i₂ := eq17214
       grind)
    | exact superpose eq17214 eq216
    | exact resolve eq216 eq17214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq17214
  have eq17260 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17252
       have r₂ := eq12355
       grind)
    | exact resolve eq17252 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17252
  have eq17533 : x = y ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9048
       have i₂ := eq17260
       grind)
    | exact superpose eq17260 eq9048
    | exact resolve eq9048 eq17260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9048 eq17260
  have eq17542 : y = (M.op x x) ∨ x = y := by grind
  clear eq17533
  have eq17833 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8 x x
       have i₂ := eq17542
       grind)
    | exact superpose eq17542 eq8
    | exact resolve eq8 eq17542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17542
  have eq17840 : y = (M.op x y) := by
    first
    | (have r₁ := eq17833
       have r₂ := eq12355
       grind)
    | exact resolve eq17833 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12355 eq17833
  have eq19794 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq8544
       grind)
    | exact superpose eq8544 eq14
    | exact resolve eq14 eq8544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8544
  have eq19823 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq19794
       have i₂ := eq17840
       grind)
    | exact superpose eq17840 eq19794
    | exact resolve eq19794 eq17840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19794
  have eq19824 : y = (M.op x x) := by grind
  clear eq19823
  have eq20553 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1415 x x
       have i₂ := eq12586
       grind)
    | exact superpose eq12586 eq1415
    | exact resolve eq1415 eq12586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415 eq12586
  have eq20635 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20553
       have r₂ := eq12063
       grind)
    | exact resolve eq20553 eq12063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12063 eq20553
  have eq20649 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq20635
       have i₂ := eq17840
       grind)
    | exact superpose eq17840 eq20635
    | exact resolve eq20635 eq17840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20635
  have eq20666 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq20649
       grind)
    | exact superpose eq20649 eq14
    | exact resolve eq14 eq20649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20649
  have eq20705 : (σ y) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq20666
       have i₂ := eq17840
       grind)
    | exact superpose eq17840 eq20666
    | exact resolve eq20666 eq17840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17840 eq20666
  have eq20706 : x = y := by grind
  clear eq20705
  have eq21176 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq20706
       grind)
    | exact superpose eq20706 eq14
    | exact resolve eq14 eq20706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21189 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2811
       have i₂ := eq20706
       grind)
    | exact superpose eq20706 eq2811
    | exact resolve eq2811 eq20706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2811
  have eq21234 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21176
       have i₂ := eq19824
       grind)
    | exact superpose eq19824 eq21176
    | exact resolve eq21176 eq19824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19824 eq21176
  have eq21235 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq21234
       have i₂ := eq21189
       grind)
    | exact superpose eq21189 eq21234
    | exact resolve eq21234 eq21189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21189 eq21234
  have eq21236 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq21235
       have i₂ := eq20706
       grind)
    | exact superpose eq20706 eq21235
    | exact resolve eq21235 eq20706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20706 eq21235
  have eq21237 : False := by grind
  exact eq21237

/-- `Equation335`: `x ◇ y = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation335 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law335 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law335.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) := by
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
  have eq16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) X1
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq43 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (M.op X0 X1)
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq8
    | exact resolve eq8 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq43
    | exact resolve eq43 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23
    | exact resolve eq23 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq59 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq27 (τ X1) X0
       grind)
    | exact superpose eq27 eq18
    | (have j1 := eq27 (τ X1) X0
       grind)
    | exact resolve eq18 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq88 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq28 X1 (τ X0)
       grind)
    | exact superpose eq28 eq17
    | (have j1 := eq28 X1 (τ X0)
       grind)
    | exact resolve eq17 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq28
  have eq93 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq37
  have eq108 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq93 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq93
    | exact resolve eq93 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq136 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (M.op X0 X1) X0
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq62
    | (have j0 := eq62 (M.op X0 X1) X0
       grind)
    | exact resolve eq62 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq146 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
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
  have eq158 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq163 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X1) (σ X0)
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X0 X1
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq29 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq224 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq44 X0 X0
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq44
    | exact resolve eq44 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq285 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq224 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq224 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq224
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq224 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq62 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq224 X0
       grind)
    | exact superpose eq224 eq62
    | (have j0 := eq62 (M.op X0 X0) (M.op X0 X0)
       grind)
    | (have r₁ := eq62 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq224 X0
       grind)
    | exact resolve eq62 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq296 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq294 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq835 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq59
    | exact resolve eq59 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq875 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq835 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq835
    | (have j0 := eq835 X0 X1
       grind)
    | exact resolve eq835 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq934 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq982 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq934 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq934
    | (have j0 := eq934 X0 X1
       grind)
    | exact resolve eq934 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq1694 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq158
       have i₂ := eq285 y x
       grind)
    | exact superpose eq285 eq158
    | (have j1 := eq285 y x
       grind)
    | exact resolve eq158 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1695 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq158
       have i₂ := eq982 x y
       grind)
    | exact superpose eq982 eq158
    | (have j1 := eq982 x y
       grind)
    | (have r₁ := eq158
       have r₂ := eq982 x y
       grind)
    | exact resolve eq158 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq1696 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq158
       have i₂ := eq875 y x
       grind)
    | exact superpose eq875 eq158
    | (have j1 := eq875 y x
       grind)
    | (have r₁ := eq158
       have r₂ := eq875 y x
       grind)
    | exact resolve eq158 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq875
  have eq1699 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq1696
  have eq1700 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1695
  have eq1701 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq1694
  have eq1885 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq2067 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq146
    | (have j0 := eq146 X1 (τ X0)
       grind)
    | exact resolve eq146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq2175 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2067 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2067
    | (have j0 := eq2067 X0 X1
       grind)
    | exact resolve eq2067 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2067
  have eq2185 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2175 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2175
    | (have j0 := eq2175 X0 X1
       grind)
    | exact resolve eq2175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq3436 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq108 x
       have i₂ := eq1699
       grind)
    | exact superpose eq1699 eq108
    | exact resolve eq108 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1699
  have eq3457 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3436
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3436
    | exact resolve eq3436 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3436
  have eq3458 : x = (k x y) := by grind
  clear eq3457
  have eq9872 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (σ x) (σ x)
       have i₂ := eq1700
       grind)
    | exact superpose eq1700 eq8
    | exact resolve eq8 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10858 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq296 (σ x)
       have i₂ := eq1701
       grind)
    | exact superpose eq1701 eq296
    | exact resolve eq296 eq1701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq1701
  have eq10871 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10858
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq10858
    | exact resolve eq10858 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10858
  have eq11064 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq10871
       grind)
    | exact superpose eq10871 eq9
    | exact resolve eq9 eq10871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10871
  have eq11161 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11064
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq11064
    | exact resolve eq11064 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11064
  have eq11163 : y = (k y y) := by
    first
    | (have j1 := eq62 y y
       grind)
    | (have r₁ := eq11161
       have r₂ := eq62 y y
       grind)
    | exact resolve eq11161 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11161
  have eq11321 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq178 y
       have i₂ := eq11163
       grind)
    | exact superpose eq11163 eq178
    | (have j0 := eq178 y
       grind)
    | exact resolve eq178 eq11163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq11330 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq285 y y
       have i₂ := eq11163
       grind)
    | exact superpose eq11163 eq285
    | (have j0 := eq285 y x
       grind)
    | exact resolve eq285 eq11163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq11333 : y = (M.op y y) := by grind
  clear eq11330
  have eq11337 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq11321
  have eq11451 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1885 (τ X0) (τ X1)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq1885
    | (have j0 := eq1885 (τ X0) (τ X1)
       grind)
    | exact resolve eq1885 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq11456 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1885 x y
       have i₂ := eq3458
       grind)
    | exact superpose eq3458 eq1885
    | (have j0 := eq1885 x y
       grind)
    | exact resolve eq1885 eq3458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq11520 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11451 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq11451
    | (have j0 := eq11451 X0 X1
       grind)
    | exact resolve eq11451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11451
  have eq11526 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11520 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq11520
    | (have j0 := eq11520 X0 X1
       grind)
    | exact resolve eq11520 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11520
  have eq11529 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11526 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11526
    | (have j0 := eq11526 X0 X1
       grind)
    | exact resolve eq11526 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11526
  have eq11530 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11529 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11529
    | (have j0 := eq11529 X0 X1
       grind)
    | exact resolve eq11529 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11529
  have eq11847 : x ≠ y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11530 x y
       have i₂ := eq3458
       grind)
    | exact superpose eq3458 eq11530
    | (have j0 := eq11530 x y
       grind)
    | exact resolve eq11530 eq3458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3458 eq11530
  have eq12031 : ∀ X0 : G, y = X0 ∨ (M.op y X0) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq11163
       have i₂ := eq2185 y X0
       grind)
    | (have i₁ := eq11163
       have i₂ := eq2185 X0 (k y y)
       grind)
    | exact superpose eq2185 eq11163
    | (have j1 := eq2185 y X0
       grind)
    | exact resolve eq11163 eq2185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2185 eq11163
  have eq12034 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq12031 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12031
  have eq16261 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq136 (σ x) (σ x)
       have i₂ := eq1700
       grind)
    | exact superpose eq1700 eq136
    | exact resolve eq136 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq1700
  have eq16307 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16261
       have r₂ := eq9872
       grind)
    | exact resolve eq16261 eq9872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9872 eq16261
  have eq16334 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16307
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq16307
    | exact resolve eq16307 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16307
  have eq18729 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq16334
       grind)
    | exact superpose eq16334 eq9
    | exact resolve eq9 eq16334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16334
  have eq18856 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18729
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq18729
    | exact resolve eq18729 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18729
  have eq19055 : y = (M.op y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12034 x
       have i₂ := eq18856
       grind)
    | exact superpose eq18856 eq12034
    | (have j0 := eq12034 (M.op y x)
       grind)
    | exact resolve eq12034 eq18856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12034 eq18856
  have eq19072 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19055
       have r₂ := eq11847
       grind)
    | exact resolve eq19055 eq11847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11847 eq19055
  have eq19269 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 x y
       have i₂ := eq19072
       grind)
    | exact superpose eq19072 eq8
    | exact resolve eq8 eq19072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19072
  have eq19291 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19269
       have i₂ := eq11333
       grind)
    | exact superpose eq11333 eq19269
    | exact resolve eq19269 eq11333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11333 eq19269
  have eq19292 : y = (M.op x y) := by grind
  clear eq19291
  have eq19324 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq8 y x
       have i₂ := eq19292
       grind)
    | exact superpose eq19292 eq8
    | exact resolve eq8 eq19292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19343 : y = (M.op y x) := by
    first
    | (have i₁ := eq19324
       have i₂ := eq19292
       grind)
    | exact superpose eq19292 eq19324
    | exact resolve eq19324 eq19292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19324
  have eq19983 : y ≠ y ∨ y = (k y x) := by
    first
    | (have i₁ := eq62 y x
       have i₂ := eq19343
       grind)
    | exact superpose eq19343 eq62
    | (have j0 := eq62 y x
       grind)
    | (have r₁ := eq62 y x
       have r₂ := eq19343
       grind)
    | exact resolve eq62 eq19343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq19343
  have eq19990 : y = (k y x) := by grind
  clear eq19983
  have eq20445 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq163 y x
       have i₂ := eq19990
       grind)
    | exact superpose eq19990 eq163
    | (have j0 := eq163 y x
       grind)
    | exact resolve eq163 eq19990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq19990
  have eq20454 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq20445
       have i₂ := eq11337
       grind)
    | exact superpose eq11337 eq20445
    | exact resolve eq20445 eq11337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20445
  have eq20455 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20454
       have i₂ := eq11337
       grind)
    | exact superpose eq11337 eq20454
    | exact resolve eq20454 eq11337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11337 eq20454
  have eq20456 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20455
       have r₂ := eq11456
       grind)
    | exact resolve eq20455 eq11456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11456 eq20455
  have eq21556 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq20456
       grind)
    | exact superpose eq20456 eq14
    | exact resolve eq14 eq20456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20456
  have eq21608 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq21556
       have i₂ := eq19292
       grind)
    | exact superpose eq19292 eq21556
    | exact resolve eq21556 eq19292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19292 eq21556
  have eq21609 : False := by grind
  exact eq21609

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation413 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq87 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq87 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq87 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq91 (σ X0) (σ X1)
       grind)
    | exact superpose eq91 eq13
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 X1
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq107
    | exact resolve eq107 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq107
  have eq1473 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq114 x y
       grind)
    | exact superpose eq114 eq14
    | (have r₁ := eq14
       have r₂ := eq114 x y
       grind)
    | exact resolve eq14 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1492 : False := by grind
  exact eq1492

/-- `Equation417`: `x = x ◇ (x ◇ (y ◇ (x ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation417 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law417 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law417.models_iff G M).mp hM
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq87 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq87 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq87 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq91 (σ X0) (σ X1)
       grind)
    | exact superpose eq91 eq13
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 X1
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq107
    | exact resolve eq107 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq107
  have eq1474 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq114 x y
       grind)
    | exact superpose eq114 eq14
    | (have r₁ := eq14
       have r₂ := eq114 x y
       grind)
    | exact resolve eq14 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1493 : False := by grind
  exact eq1493

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation418 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
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
  have eq45 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X1
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
  have eq425 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq426 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq425 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq432 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq426 (σ X0) (σ X1)
       grind)
    | exact superpose eq426 eq13
    | exact resolve eq13 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq432 X0 X1
       have i₂ := eq426 X0 X1
       grind)
    | exact superpose eq426 eq432
    | exact resolve eq432 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426 eq432
  have eq1184 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq445 x y
       grind)
    | exact superpose eq445 eq14
    | (have r₁ := eq14
       have r₂ := eq445 x y
       grind)
    | exact resolve eq14 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq1208 : False := by grind
  exact eq1208

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation419 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq88 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq88 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq92 (σ X0) (σ X1)
       grind)
    | exact superpose eq92 eq13
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq108
    | exact resolve eq108 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq108
  have eq1315 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq115 x y
       grind)
    | exact superpose eq115 eq14
    | (have r₁ := eq14
       have r₂ := eq115 x y
       grind)
    | exact resolve eq14 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1336 : False := by grind
  exact eq1336
