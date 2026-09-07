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

/-- `Equation3272`: `x ◇ x = y ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3272 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3272 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3272.models_iff G M).mp hM
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
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq158 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq164 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq158 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq158 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq158 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq158 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq186 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq164 (σ X0) (σ X1)
       grind)
    | exact superpose eq164 eq13
    | exact resolve eq13 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 X1
       have i₂ := eq164 X0 X1
       grind)
    | exact superpose eq164 eq186
    | exact resolve eq186 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq186
  have eq1472 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq196 x y
       grind)
    | exact superpose eq196 eq14
    | (have r₁ := eq14
       have r₂ := eq196 x y
       grind)
    | exact resolve eq14 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq1503 : False := by grind
  exact eq1503

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
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
  have eq24 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op X1 x)
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 X1
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq8
    | exact resolve eq8 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 X2)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq24 X0 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq75 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq80 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq84 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X0 X1 X2
       have i₂ := eq34 X2 X2
       grind)
    | exact superpose eq34 eq70
    | (have j0 := eq70 X0 X1 X2
       grind)
    | exact resolve eq70 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq70
  have eq511 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq525 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq511 X0 X1
       have j1 := eq84 X0 X1 x
       grind)
    | (have r₁ := eq511 x x
       have r₂ := eq84 x x x
       grind)
    | (have r₁ := eq511 X0 X1
       have r₂ := eq84 X0 X1 X0
       grind)
    | exact resolve eq511 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq511
  have eq554 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq525 (σ X0) (σ X1)
       grind)
    | exact superpose eq525 eq13
    | exact resolve eq13 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 X1
       have i₂ := eq525 X0 X1
       grind)
    | exact superpose eq525 eq554
    | exact resolve eq554 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq554
  have eq6563 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq565 x y
       grind)
    | exact superpose eq565 eq14
    | (have r₁ := eq14
       have r₂ := eq565 x y
       grind)
    | exact resolve eq14 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq6632 : False := by grind
  exact eq6632

/-- `Equation3274`: `x ◇ x = y ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3274 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3274 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3274.models_iff G M).mp hM
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq156 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq160 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq156 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq156 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq156 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq156 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq179 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq160 (σ X0) (σ X1)
       grind)
    | exact superpose eq160 eq13
    | exact resolve eq13 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 X1
       have i₂ := eq160 X0 X1
       grind)
    | exact superpose eq160 eq179
    | exact resolve eq179 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq179
  have eq1516 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq188 x y
       grind)
    | exact superpose eq188 eq14
    | (have r₁ := eq14
       have r₂ := eq188 x y
       grind)
    | exact resolve eq14 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq1546 : False := by grind
  exact eq1546

/-- `Equation3284`: `x ◇ x = y ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3284 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3284 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3284.models_iff G M).mp hM
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
  have eq260 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq266 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq260 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq260 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq260 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq260 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq288 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq266 (σ X0) (σ X1)
       grind)
    | exact superpose eq266 eq13
    | exact resolve eq13 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq288 X0 X1
       have i₂ := eq266 X0 X1
       grind)
    | exact superpose eq266 eq288
    | exact resolve eq288 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq288
  have eq1149 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq298 x y
       grind)
    | exact superpose eq298 eq14
    | (have r₁ := eq14
       have r₂ := eq298 x y
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq1173 : False := by grind
  exact eq1173

/-- `Equation329`: `x ◇ y = x ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation329 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law329 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law329.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
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
  have eq17 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22
    | exact resolve eq22 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq31 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = X0 ∨ (M.op X0 (M.op X1 X2)) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 X2) X2 X1
       have i₂ := eq12 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 (M.op X2 X1))
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X1 X2) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq35 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k (M.op X1 X2) X0) ∨ (M.op (M.op X1 X2) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X0 X1 X2
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq32
    | (have j0 := eq32 X0 X1 X2
       grind)
    | exact resolve eq32 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq38 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq20
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq20 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq54 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq74 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq26 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq26
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (k X0 X2) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq31 X1 X0 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq31 X0 X0 X2
       grind)
    | exact superpose eq31 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq31 X2 X1 X0
       grind)
    | exact resolve eq12 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X2 (σ X1)) = (M.op X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq31 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq31 eq13
    | (have j1 := eq31 (σ X1) X2 (σ X0)
       grind)
    | exact resolve eq13 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq43
  have eq151 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq136 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq136
    | exact resolve eq136 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq181 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op X0 X2) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X1 X2
       have i₂ := eq35 X0 X1 X2
       grind)
    | (have i₁ := eq17 X0 X1
       have i₂ := eq35 (M.op (M.op X0 X1) X1) X1 X2
       grind)
    | exact superpose eq35 eq17
    | (have j1 := eq35 X0 X1 X2
       grind)
    | exact resolve eq17 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq35
  have eq197 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op X2 X1) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq51
    | (have j0 := eq51 (M.op X2 X1) X0
       grind)
    | (have r₁ := eq51 (M.op X0 X1) X0
       have r₂ := eq8 X0 X1 X0
       grind)
    | exact resolve eq51 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X1 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq33
    | (have j0 := eq33 X0 X1
       have j1 := eq33 X0 X1
       grind)
    | exact resolve eq33 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
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
  have eq287 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq288 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (σ X0) (σ X1)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq8
    | (have j1 := eq33 X1 X0
       grind)
    | exact resolve eq8 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq9
    | (have j1 := eq33 X1 X0
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq287 X0
       have i₂ := eq13 X0 (k X0 X0)
       grind)
    | exact superpose eq13 eq287
    | (have j0 := eq287 X0
       grind)
    | exact resolve eq287 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq335 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq151 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq151
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq151 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq336 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq151 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq151 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq151
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq151 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq335 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq335
    | (have j0 := eq335 X0 X1
       grind)
    | exact resolve eq335 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq714 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq313 (τ X0)
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq313
    | (have j0 := eq313 (τ X0)
       grind)
    | exact resolve eq313 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq714 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq714
    | (have j0 := eq714 X0
       grind)
    | exact resolve eq714 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq719 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq716 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq716
    | (have j0 := eq716 X0
       grind)
    | exact resolve eq716 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq729 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq719 (τ X0)
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq719
    | (have j0 := eq719 (τ X0)
       grind)
    | exact resolve eq719 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq741 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq38
    | exact resolve eq38 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq10
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq10 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq823 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq741 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq741
    | (have j0 := eq741 X0 X1
       grind)
    | exact resolve eq741 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq888 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq903 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (σ (k (τ X1) X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1
       have i₂ := eq823 X0 (τ X1)
       grind)
    | (have i₁ := eq26 X0
       have i₂ := eq823 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq823 eq26
    | (have j1 := eq823 X0 (τ X1)
       grind)
    | exact resolve eq26 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq908 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq903 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq903
    | (have j0 := eq903 X0 X1
       grind)
    | exact resolve eq903 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq1565 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq46 y x
       grind)
    | exact superpose eq46 eq14
    | (have j1 := eq46 y x
       grind)
    | exact resolve eq14 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1571 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq46 X0 X0
       grind)
    | exact superpose eq46 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq46 X0 X0
       grind)
    | exact resolve eq12 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq1810 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq320 (τ X0)
       grind)
    | exact superpose eq320 eq19
    | (have j1 := eq320 (τ X0)
       grind)
    | exact resolve eq19 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq1847 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1810 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq1810
    | (have j0 := eq1810 X0
       grind)
    | exact resolve eq1810 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1810
  have eq1853 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1847 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1847
    | (have j0 := eq1847 X0
       grind)
    | exact resolve eq1847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847
  have eq1856 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1853 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1853
    | (have j0 := eq1853 X0
       grind)
    | exact resolve eq1853 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq2292 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq74
    | (have j0 := eq74 X1 (σ X0)
       grind)
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2314 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq313 (τ X0)
       have i₂ := eq74 (τ X0) X0
       grind)
    | exact superpose eq74 eq313
    | (have j0 := eq313 (τ X0)
       have j1 := eq74 (τ X0) X0
       grind)
    | exact resolve eq313 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq2357 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2314 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2314
    | (have j0 := eq2314 X0
       grind)
    | exact resolve eq2314 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2314
  have eq2369 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2292 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2292
    | (have j0 := eq2292 X0 X1
       grind)
    | exact resolve eq2292 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2292
  have eq2382 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2357 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2357
    | (have j0 := eq2357 X0
       grind)
    | exact resolve eq2357 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2357
  have eq2398 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq2382 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2382
    | (have j0 := eq2382 X0
       grind)
    | exact resolve eq2382 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2382
  have eq2411 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2398 X0
       have j1 := eq51 X0 X0
       grind)
    | (have r₁ := eq2398 X0
       have r₂ := eq51 X0 X0
       grind)
    | exact resolve eq2398 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2398
  have eq2604 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2411 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2411
    | (have j0 := eq2411 (σ X0)
       grind)
    | exact resolve eq2411 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2411
  have eq2636 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2604 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq2604
    | (have j0 := eq2604 X0
       grind)
    | exact resolve eq2604 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2604
  have eq2862 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq313 X0
       have i₂ := eq2369 X0 X0
       grind)
    | exact superpose eq2369 eq313
    | (have j0 := eq313 X0
       have j1 := eq2369 X0 X0
       grind)
    | (have r₁ := eq313 x
       have r₂ := eq2369 x x
       grind)
    | exact resolve eq313 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369
  have eq2889 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2862 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862
  have eq3016 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq181 X2 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3993 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq109 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq3994 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3993 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3993
  have eq4229 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq122 x y X0
       grind)
    | exact superpose eq122 eq14
    | (have j1 := eq122 x y X0
       grind)
    | exact resolve eq14 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4341 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq122 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq5377 : ∀ X0 X1 X2 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op X2 (σ X1)) = (M.op X2 (σ (k X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq151 X1
       have i₂ := eq288 X1 X0 X2
       grind)
    | exact superpose eq288 eq151
    | (have j1 := eq288 X1 X0 X2
       grind)
    | exact resolve eq151 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq288
  have eq5422 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op X2 (σ (k X1 X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5377 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq5377
    | (have j0 := eq5377 X0 X1 X2
       grind)
    | exact resolve eq5377 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5377
  have eq8579 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (τ X0) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq336
    | (have j0 := eq336 X1 (τ X0)
       grind)
    | exact resolve eq336 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq8693 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8579 X0 X1
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq8579
    | (have j0 := eq8579 X0 X1
       grind)
    | exact resolve eq8579 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8579
  have eq9821 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq360 x y
       grind)
    | exact superpose eq360 eq14
    | (have j1 := eq360 x y
       grind)
    | exact resolve eq14 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq9893 : y = (k y x) := by
    first
    | (have j1 := eq888 x y
       grind)
    | (have r₁ := eq9821
       have r₂ := eq888 x y
       grind)
    | exact resolve eq9821 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9821
  have eq10267 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq823 x y
       have i₂ := eq9893
       grind)
    | exact superpose eq9893 eq823
    | (have j0 := eq823 x y
       grind)
    | exact resolve eq823 eq9893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11012 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq269 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq269 X0 X1
       grind)
    | exact superpose eq269 eq9
    | (have j1 := eq269 X0 X1
       grind)
    | exact resolve eq9 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq11072 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11012 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq11012
    | (have j0 := eq11012 X0 X1
       grind)
    | exact resolve eq11012 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11012
  have eq16586 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq729 X0
       have i₂ := eq8693 X0 X0
       grind)
    | exact superpose eq8693 eq729
    | (have j0 := eq729 X0
       have j1 := eq8693 X0 X0
       grind)
    | (have r₁ := eq729 x
       have r₂ := eq8693 x x
       grind)
    | exact resolve eq729 eq8693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729 eq8693
  have eq16594 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq16586 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16586
  have eq25712 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16594 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq16594
    | (have j0 := eq16594 (σ X0)
       grind)
    | exact resolve eq16594 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16594
  have eq25851 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25712 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq25712
    | (have j0 := eq25712 X0
       grind)
    | exact resolve eq25712 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25712
  have eq34239 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq34246 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34239 X1 X1
       have i₂ := eq823 X0 X1
       grind)
    | (have i₁ := eq34239 X0 X1
       have i₂ := eq823 (M.op X0 X1) X1
       grind)
    | exact superpose eq823 eq34239
    | (have j1 := eq823 X0 X1
       grind)
    | exact resolve eq34239 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34248 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq34239 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq34239 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq34239
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq34239 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34393 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (M.op (σ X0) X1) X0
       have i₂ := eq34239 (σ X0) X1
       grind)
    | exact superpose eq34239 eq25
    | exact resolve eq25 eq34239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq34239
  have eq34562 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq773 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq773
    | (have j0 := eq773 X1 (σ X0)
       grind)
    | exact resolve eq773 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34903 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq773 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq34904 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq34903 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34903
    | (have j0 := eq34903 X0
       grind)
    | exact resolve eq34903 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34903
  have eq34956 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34562 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq34562
    | (have j0 := eq34562 X0 X1
       grind)
    | exact resolve eq34562 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34562
  have eq35186 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq34248 (τ X0) X1
       grind)
    | exact superpose eq34248 eq19
    | (have j1 := eq34248 (τ X0) X1
       grind)
    | exact resolve eq19 eq34248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35309 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35186 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq35186
    | (have j0 := eq35186 X0 X1
       grind)
    | exact resolve eq35186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35186
  have eq36004 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1565
       have i₂ := eq3994 y x
       grind)
    | exact superpose eq3994 eq1565
    | (have j1 := eq3994 y x
       grind)
    | exact resolve eq1565 eq3994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq36013 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq36004
  have eq37719 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34904 X0
       have i₂ := eq34248 X0 X0
       grind)
    | exact superpose eq34248 eq34904
    | (have j0 := eq34904 X0
       have j1 := eq34248 X0 X0
       grind)
    | (have r₁ := eq34904 x
       have r₂ := eq34248 x x
       grind)
    | exact resolve eq34904 eq34248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34248
  have eq37758 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq37719 X0
       have j1 := eq34904 X0
       grind)
    | (have r₁ := eq37719 X0
       have r₂ := eq34904 X0
       grind)
    | exact resolve eq37719 eq34904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34904 eq37719
  have eq38497 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34393 X0 (σ X0)
       have i₂ := eq295 X0 X1
       grind)
    | (have i₁ := eq34393 X0 X1
       have i₂ := eq295 X0 (τ (M.op (σ X0) X1))
       grind)
    | exact superpose eq295 eq34393
    | (have j1 := eq295 X1 X0
       grind)
    | exact resolve eq34393 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq34393
  have eq39211 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq37758 (σ X0)
       have i₂ := eq2889 X0
       grind)
    | exact superpose eq2889 eq37758
    | (have j0 := eq37758 (σ X0)
       have j1 := eq2889 X0
       grind)
    | (have r₁ := eq37758 (σ X0)
       have r₂ := eq2889 X0
       grind)
    | exact resolve eq37758 eq2889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2889 eq37758
  have eq39225 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq39211 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39211
  have eq39234 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq39225 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq39225
    | (have j0 := eq39225 X0
       grind)
    | exact resolve eq39225 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39225
  have eq44443 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39234 X1
       have i₂ := eq823 X0 X1
       grind)
    | (have i₁ := eq39234 X0
       have i₂ := eq823 (M.op X0 X0) X1
       grind)
    | exact superpose eq823 eq39234
    | (have j1 := eq823 X0 X1
       grind)
    | exact resolve eq39234 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39234
  have eq48641 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq4229 X0
       have i₂ := eq3994 y x
       grind)
    | exact superpose eq3994 eq4229
    | (have j0 := eq4229 X0
       have j1 := eq3994 y x
       grind)
    | exact resolve eq4229 eq3994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4229
  have eq48656 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq48641 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48641
  have eq49658 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq48656 (σ x)
       grind)
    | exact superpose eq48656 eq14
    | exact resolve eq14 eq48656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48656
  have eq55496 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq35309 (σ X0) X1
       grind)
    | exact superpose eq35309 eq13
    | (have j1 := eq35309 (σ X0) X1
       grind)
    | exact resolve eq13 eq35309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35309
  have eq55688 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55496 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq55496
    | (have j0 := eq55496 X0 X1
       grind)
    | exact resolve eq55496 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55496
  have eq59187 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq38497 x y
       grind)
    | exact superpose eq38497 eq14
    | (have j1 := eq38497 x y
       grind)
    | exact resolve eq14 eq38497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38497
  have eq59334 : x = (k x y) := by
    first
    | (have j1 := eq34246 x y
       grind)
    | (have r₁ := eq59187
       have r₂ := eq34246 x y
       grind)
    | exact resolve eq59187 eq34246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34246 eq59187
  have eq59420 : ∀ X0 : G, x = (M.op y x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq31 y X0 x
       have i₂ := eq59334
       grind)
    | exact superpose eq59334 eq31
    | (have j0 := eq31 y X0 x
       grind)
    | exact resolve eq31 eq59334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq85854 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq908 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq908
    | (have j0 := eq908 X1 (σ X0)
       grind)
    | exact resolve eq908 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq86203 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85854 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq85854
    | (have j0 := eq85854 X0 X1
       grind)
    | exact resolve eq85854 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85854
  have eq86234 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86203 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq86203
    | (have j0 := eq86203 X0 X1
       grind)
    | exact resolve eq86203 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86203
  have eq93206 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4341 (τ X0) (τ X1)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq4341
    | exact resolve eq4341 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq4341
  have eq93292 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq93206 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93206
    | (have j0 := eq93206 X0 X1
       grind)
    | exact resolve eq93206 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93206
  have eq93346 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq93292 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq93292
    | (have j0 := eq93292 X0 X1
       grind)
    | exact resolve eq93292 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93292
  have eq93362 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq93346 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93346
    | (have j0 := eq93346 X0 X1
       grind)
    | exact resolve eq93346 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93346
  have eq93368 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq93362 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq93362
    | (have j0 := eq93362 X0 X1
       grind)
    | exact resolve eq93362 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93362
  have eq93369 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq93368 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq93368
    | (have j0 := eq93368 X0 X1
       grind)
    | exact resolve eq93368 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93368
  have eq94489 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X2) ∨ (M.op X0 X1) = (M.op X2 (M.op X0 X1)) ∨ (M.op X2 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93369 (M.op X1 X2) X0
       have i₂ := eq181 X0 X1 X2
       grind)
    | exact superpose eq181 eq93369
    | (have j1 := eq181 X2 X0 X1
       grind)
    | (have r₁ := eq93369 (M.op X2 X2) X2
       have r₂ := eq181 X2 X2 X2
       grind)
    | (have r₁ := eq93369 (M.op X1 X2) X2
       have r₂ := eq181 X2 X1 X2
       grind)
    | exact resolve eq93369 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq93369
  have eq94638 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X0 X1) ≠ (M.op X2 X2) ∨ (M.op X2 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94489 X0 X1 X2
       have i₂ := eq8 X2 X1 X0
       grind)
    | exact superpose eq8 eq94489
    | (have j0 := eq94489 X0 X1 X2
       grind)
    | (have r₁ := eq94489 (M.op X2 X1) X1 (M.op X2 X1)
       have r₂ := eq8 (M.op X2 X1) X1 X2
       grind)
    | (have r₁ := eq94489 X1 (M.op X2 X1) X1
       have r₂ := eq8 X1 X1 X2
       grind)
    | exact resolve eq94489 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94489
  have eq94642 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X2) ∨ (M.op X2 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq94638 X0 X1 X2
       have j1 := eq3016 X0 X1 X2
       grind)
    | (have r₁ := eq94638 X0 X1 X2
       have r₂ := eq3016 X0 X1 X2
       grind)
    | (have r₁ := eq94638 X2 X1 X0
       have r₂ := eq3016 X0 X1 X2
       grind)
    | exact resolve eq94638 eq3016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94638
  have eq98098 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq11072 x y
       grind)
    | exact superpose eq11072 eq14
    | (have j1 := eq11072 x y
       grind)
    | exact resolve eq14 eq11072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11072
  have eq98527 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq44443 x y
       grind)
    | (have r₁ := eq98098
       have r₂ := eq44443 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq98098
       have r₂ := eq44443 (k y x) (M.op x y)
       grind)
    | (have r₁ := eq98098
       have r₂ := eq44443 x y
       grind)
    | exact resolve eq98098 eq44443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44443 eq98098
  have eq98849 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55688 y y
       have i₂ := eq98527
       grind)
    | exact superpose eq98527 eq55688
    | exact resolve eq55688 eq98527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55688 eq98527
  have eq98855 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq98849
  have eq98878 : x = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq59420 y
       have i₂ := eq98855
       grind)
    | exact superpose eq98855 eq59420
    | exact resolve eq59420 eq98855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59420 eq98855
  have eq98942 : x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq98878
  have eq109578 : (σ x) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq34956 y x
       have i₂ := eq59334
       grind)
    | exact superpose eq59334 eq34956
    | (have j0 := eq34956 y x
       grind)
    | exact resolve eq34956 eq59334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59334
  have eq109778 : (M.op y x) = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9 (M.op y x)
       have i₂ := eq109578
       grind)
    | exact superpose eq109578 eq9
    | exact resolve eq9 eq109578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109578
  have eq109817 : (σ y) = (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq109778
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq109778
    | exact resolve eq109778 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109778
  have eq109827 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2636 x
       have i₂ := eq109817
       grind)
    | exact superpose eq109817 eq2636
    | (have j0 := eq2636 x
       grind)
    | exact resolve eq2636 eq109817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2636 eq109817
  have eq109893 : (σ x) = (σ (k x x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq109827
       have r₂ := eq98942
       grind)
    | exact resolve eq109827 eq98942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109827
  have eq109927 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq313 x
       have i₂ := eq109893
       grind)
    | exact superpose eq109893 eq313
    | (have j0 := eq313 x
       grind)
    | (have r₁ := eq313 x
       have r₂ := eq109893
       grind)
    | exact resolve eq313 eq109893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109893
  have eq109983 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq109927
  have eq110556 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq49658
       have i₂ := eq109983
       grind)
    | exact superpose eq109983 eq49658
    | exact resolve eq49658 eq109983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49658 eq109983
  have eq110638 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y x) := by grind
  clear eq110556
  have eq110687 : (σ x) ≠ (σ y) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq110638
       have i₂ := eq36013
       grind)
    | exact superpose eq36013 eq110638
    | exact resolve eq110638 eq36013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36013 eq110638
  have eq110691 : (σ x) ≠ (σ y) ∨ x = (M.op y x) := by grind
  clear eq110687
  have eq110693 : x = (M.op y x) := by
    first
    | (have r₁ := eq110691
       have r₂ := eq98942
       grind)
    | exact resolve eq110691 eq98942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98942 eq110691
  have eq111691 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1571 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1571
  have eq111692 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq111691 X0 X1
       have j1 := eq270 X1 X0
       grind)
    | (have r₁ := eq111691 (k X1 X1) X0
       have r₂ := eq270 X0 X1
       grind)
    | (have r₁ := eq111691 X0 (σ (k X1 X1))
       have r₂ := eq270 (σ X0) X1
       grind)
    | (have r₁ := eq111691 X1 X0
       have r₂ := eq270 X0 X1
       grind)
    | exact resolve eq111691 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq111691
  have eq111741 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X1)
       have i₂ := eq111692 (τ X1) X0
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq111692 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq111692 eq19
    | (have j1 := eq111692 (τ X1) X0
       grind)
    | exact resolve eq19 eq111692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq111742 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq111692 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq111692 X0 (σ X0)
       grind)
    | exact superpose eq111692 eq9
    | (have j1 := eq111692 X1 X0
       grind)
    | exact resolve eq9 eq111692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111692
  have eq111784 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq111741 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq111741
    | (have j0 := eq111741 X0 X1
       grind)
    | exact resolve eq111741 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111741
  have eq111792 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq111784 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq111784
    | (have j0 := eq111784 X0 X1
       grind)
    | exact resolve eq111784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111784
  have eq111928 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq112579 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq111742 (σ X0) X1
       grind)
    | exact superpose eq111742 eq13
    | (have j1 := eq111742 (σ X0) X1
       grind)
    | exact resolve eq13 eq111742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111742
  have eq112607 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq112579 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq112579
    | (have j0 := eq112579 X0 X1
       grind)
    | exact resolve eq112579 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112579
  have eq113966 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq112607 x y
       grind)
    | exact superpose eq112607 eq14
    | (have j1 := eq112607 x y
       grind)
    | exact resolve eq14 eq112607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114044 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq113966
       have i₂ := eq9893
       grind)
    | exact superpose eq9893 eq113966
    | exact resolve eq113966 eq9893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9893 eq113966
  have eq114100 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq114044
       have i₂ := eq10267
       grind)
    | exact superpose eq10267 eq114044
    | (have r₁ := eq114044
       have r₂ := eq10267
       grind)
    | exact resolve eq114044 eq10267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10267 eq114044
  have eq114104 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq114100
  have eq114224 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3994 y y
       have i₂ := eq114104
       grind)
    | exact superpose eq114104 eq3994
    | (have j0 := eq3994 y y
       grind)
    | exact resolve eq3994 eq114104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3994
  have eq114250 : x = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq111792 y y
       have i₂ := eq114104
       grind)
    | exact superpose eq114104 eq111792
    | exact resolve eq111792 eq114104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111792 eq114104
  have eq114255 : x = (M.op y y) ∨ x = y := by grind
  clear eq114250
  have eq114267 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq114224
  have eq114658 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq114267
  have eq114673 : x = (M.op y y) := by
    first
    | (have r₁ := eq114658
       have r₂ := eq114255
       grind)
    | exact resolve eq114658 eq114255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114255 eq114658
  have eq114726 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 y y
       have i₂ := eq114673
       grind)
    | exact superpose eq114673 eq8
    | exact resolve eq8 eq114673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114787 : ∀ X0 : G, x ≠ (M.op X0 y) ∨ x = (k (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq3016 X0 y y
       have i₂ := eq114673
       grind)
    | exact superpose eq114673 eq3016
    | exact resolve eq3016 eq114673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3016
  have eq115003 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq38 X0 y
       have i₂ := eq114726 (τ X0)
       grind)
    | exact superpose eq114726 eq38
    | (have j0 := eq38 X0 y
       grind)
    | exact resolve eq38 eq114726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq115063 : ∀ X0 : G, (τ X0) = (M.op y x) ∨ (k (σ y) X0) = (σ (M.op (τ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq115003 X0
       have i₂ := eq114726 y
       grind)
    | exact superpose eq114726 eq115003
    | (have j0 := eq115003 X0
       grind)
    | exact resolve eq115003 eq114726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115003
  have eq115183 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) x)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq115063 X0
       have i₂ := eq110693
       grind)
    | exact superpose eq110693 eq115063
    | (have j0 := eq115063 X0
       grind)
    | exact resolve eq115063 eq110693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115063
  have eq118028 : x ≠ y ∨ x = (k y y) ∨ (M.op y y) = (k y y) := by
    first
    | (have i₁ := eq114787 (M.op y y)
       have i₂ := eq111928 y
       grind)
    | exact superpose eq111928 eq114787
    | (have j1 := eq111928 y
       grind)
    | exact resolve eq114787 eq111928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111928 eq114787
  have eq118048 : (M.op y x) = (k y y) ∨ x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq118028
       have i₂ := eq114726 y
       grind)
    | exact superpose eq114726 eq118028
    | exact resolve eq118028 eq114726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118028
  have eq118055 : x = (k y y) ∨ x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq118048
       have i₂ := eq110693
       grind)
    | exact superpose eq110693 eq118048
    | exact resolve eq118048 eq110693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118048
  have eq118056 : x ≠ y ∨ x = (k y y) := by grind
  clear eq118055
  have eq123587 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq115183 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq115183
    | exact resolve eq115183 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115183
  have eq123661 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq123587 X0
       have i₂ := eq13 y X0
       grind)
    | exact superpose eq13 eq123587
    | (have j0 := eq123587 X0
       grind)
    | exact resolve eq123587 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123587
  have eq123806 : ∀ X0 : G, (k y X0) = (τ (σ (M.op X0 x))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq9 (k y X0)
       have i₂ := eq123661 X0
       grind)
    | exact superpose eq123661 eq9
    | (have j1 := eq123661 X0
       grind)
    | exact resolve eq9 eq123661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123661
  have eq123861 : ∀ X0 : G, (k y X0) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq123806 X0
       have i₂ := eq9 (M.op X0 x)
       grind)
    | exact superpose eq9 eq123806
    | (have j0 := eq123806 X0
       grind)
    | exact resolve eq123806 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123806
  have eq124199 : y = (M.op (k y y) x) ∨ y = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1856 y
       have i₂ := eq123861 (k y y)
       grind)
    | exact superpose eq123861 eq1856
    | (have j0 := eq1856 y
       have j1 := eq123861 (k y y)
       grind)
    | exact resolve eq1856 eq123861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1856
  have eq124222 : y = (M.op y x) ∨ y = (M.op (k y y) x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq124199
       have i₂ := eq114726 y
       grind)
    | exact superpose eq114726 eq124199
    | exact resolve eq124199 eq114726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124199
  have eq124289 : x = y ∨ y = (M.op (k y y) x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq124222
       have i₂ := eq110693
       grind)
    | exact superpose eq110693 eq124222
    | exact resolve eq124222 eq110693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124222
  have eq124307 : y = (M.op (k y y) x) ∨ x = (k y y) := by
    first
    | (have r₁ := eq124289
       have r₂ := eq118056
       grind)
    | exact resolve eq124289 eq118056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118056 eq124289
  have eq133613 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq313 X0
       have i₂ := eq86234 X0 X0
       grind)
    | exact superpose eq86234 eq313
    | (have j0 := eq313 X0
       have j1 := eq86234 X0 X0
       grind)
    | (have r₁ := eq313 x
       have r₂ := eq86234 x x
       grind)
    | exact resolve eq313 eq86234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86234
  have eq133652 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq133613 X0
       have j1 := eq313 X0
       grind)
    | (have r₁ := eq133613 X0
       have r₂ := eq313 X0
       grind)
    | exact resolve eq133613 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq133613
  have eq134081 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq133652 y
       have i₂ := eq114673
       grind)
    | exact superpose eq114673 eq133652
    | (have j0 := eq133652 y
       grind)
    | exact resolve eq133652 eq114673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134316 : ∀ X0 X1 : G, (M.op X0 X1) ≠ x ∨ (M.op y X1) = (k (M.op X0 X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq94642 X0 X1 y
       have i₂ := eq114673
       grind)
    | exact superpose eq114673 eq94642
    | (have j0 := eq94642 X0 X1 y
       grind)
    | exact resolve eq94642 eq114673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94642
  have eq134529 : x ≠ y ∨ (M.op y x) = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq134316 (k y y) x
       have i₂ := eq124307
       grind)
    | exact superpose eq124307 eq134316
    | exact resolve eq134316 eq124307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124307 eq134316
  have eq134559 : (M.op y x) = (k y y) ∨ x = (k y y) := by
    first
    | (have j1 := eq123861 y
       grind)
    | (have r₁ := eq134529
       have r₂ := eq123861 y
       grind)
    | exact resolve eq134529 eq123861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123861 eq134529
  have eq134577 : x = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq134559
       have i₂ := eq110693
       grind)
    | exact superpose eq110693 eq134559
    | exact resolve eq134559 eq110693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110693 eq134559
  have eq134578 : x = (k y y) := by grind
  clear eq134577
  have eq134770 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq5422 y y x
       have i₂ := eq134578
       grind)
    | exact superpose eq134578 eq5422
    | exact resolve eq5422 eq134578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5422 eq134578
  have eq134974 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq134770 (σ x)
       grind)
    | exact superpose eq134770 eq14
    | exact resolve eq14 eq134770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134770
  have eq134996 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq134974
       have i₂ := eq114726 x
       grind)
    | exact superpose eq114726 eq134974
    | exact resolve eq134974 eq114726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114726 eq134974
  have eq135913 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq134996
       have i₂ := eq112607 x x
       grind)
    | exact superpose eq112607 eq134996
    | (have j1 := eq112607 x x
       grind)
    | exact resolve eq134996 eq112607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112607
  have eq135916 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq134996
       have i₂ := eq25851 x
       grind)
    | exact superpose eq25851 eq134996
    | (have j1 := eq25851 x
       grind)
    | exact resolve eq134996 eq25851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25851
  have eq135928 : x = (M.op x x) ∨ x = y := by
    first
    | (have j1 := eq823 x x
       grind)
    | (have r₁ := eq135916
       have r₂ := eq823 x x
       grind)
    | exact resolve eq135916 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823 eq135916
  have eq135930 : x = (k x x) ∨ x = y := by
    first
    | (have j1 := eq888 x x
       grind)
    | (have r₁ := eq135913
       have r₂ := eq888 x x
       grind)
    | exact resolve eq135913 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq135913
  have eq135972 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq133652 x
       have i₂ := eq135928
       grind)
    | exact superpose eq135928 eq133652
    | (have j0 := eq133652 x
       grind)
    | exact resolve eq133652 eq135928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133652 eq135928
  have eq136060 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq135972
  have eq136199 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq34956 x x
       have i₂ := eq135930
       grind)
    | exact superpose eq135930 eq34956
    | (have j0 := eq34956 x x
       grind)
    | exact resolve eq34956 eq135930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34956 eq135930
  have eq136203 : (σ x) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq136199
  have eq136882 : (σ x) ≠ (σ (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq134996
       have i₂ := eq136060
       grind)
    | exact superpose eq136060 eq134996
    | exact resolve eq134996 eq136060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134996 eq136060
  have eq137014 : (σ x) ≠ (σ (M.op x x)) ∨ x = y := by grind
  clear eq136882
  have eq137061 : x = y := by
    first
    | (have r₁ := eq137014
       have r₂ := eq136203
       grind)
    | exact resolve eq137014 eq136203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136203 eq137014
  have eq137075 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq137061
       grind)
    | exact superpose eq137061 eq14
    | exact resolve eq14 eq137061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137144 : x = (M.op x x) := by
    first
    | (have i₁ := eq114673
       have i₂ := eq137061
       grind)
    | exact superpose eq137061 eq114673
    | exact resolve eq114673 eq137061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114673
  have eq137198 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq134081
       have i₂ := eq137061
       grind)
    | exact superpose eq137061 eq134081
    | exact resolve eq134081 eq137061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134081 eq137061
  have eq137203 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq137198
  have eq137245 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq137075
       have i₂ := eq137144
       grind)
    | exact superpose eq137144 eq137075
    | exact resolve eq137075 eq137144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137075 eq137144
  have eq137250 : False := by grind
  exact eq137250

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

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3292 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
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
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq255 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq261 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq255 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq255 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq255 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq255 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq283 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq261 (σ X0) (σ X1)
       grind)
    | exact superpose eq261 eq13
    | exact resolve eq13 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq283 X0 X1
       have i₂ := eq261 X0 X1
       grind)
    | exact superpose eq261 eq283
    | exact resolve eq283 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq283
  have eq1235 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq293 x y
       grind)
    | exact superpose eq293 eq14
    | (have r₁ := eq14
       have r₂ := eq293 x y
       grind)
    | exact resolve eq14 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq1260 : False := by grind
  exact eq1260
