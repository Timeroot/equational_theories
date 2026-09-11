import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq63
    | exact resolve eq63 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq63
  have eq88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq98 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq100 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq98
    | (have j0 := eq98 X0 X1
       grind)
    | exact resolve eq98 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq111 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq100
    | (have j0 := eq100 (τ X0) X1
       grind)
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq268 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq251 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq251
    | (have j0 := eq251 X0 X1
       grind)
    | exact resolve eq251 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq251
  have eq274 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq268 X0 X1
       have j1 := eq111 X1 X0
       grind)
    | (have r₁ := eq268 X0 (M.op (τ X0) (τ X0))
       have r₂ := eq111 (M.op (τ X0) (τ X0)) X1
       grind)
    | (have r₁ := eq268 X0 X0
       have r₂ := eq111 X0 X1
       grind)
    | exact resolve eq268 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq268
  have eq280 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq274 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq274
    | (have j0 := eq274 X0 X1
       grind)
    | exact resolve eq274 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq925 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq280
    | (have j0 := eq280 X1 (τ X0)
       grind)
    | exact resolve eq280 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq280 (σ X1) X0
       grind)
    | exact superpose eq280 eq15
    | (have j1 := eq280 (σ X1) X0
       grind)
    | exact resolve eq15 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq949 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq936 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq936
    | (have j0 := eq936 X0 X1
       grind)
    | exact resolve eq936 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq954 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq925 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq925
    | (have j0 := eq925 X0 X1
       grind)
    | exact resolve eq925 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq1014 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1
       have i₂ := eq954 X0 (τ X1)
       grind)
    | (have i₁ := eq68 X0
       have i₂ := eq954 (τ X0) X1
       grind)
    | exact superpose eq954 eq68
    | (have j1 := eq954 X0 (τ X1)
       grind)
    | exact resolve eq68 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq954
  have eq2645 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1014 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1014
    | (have j0 := eq1014 X1 (σ X0)
       grind)
    | exact resolve eq1014 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq2679 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2645 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq2645
    | (have j0 := eq2645 X0 X1
       grind)
    | exact resolve eq2645 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2645
  have eq4002 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq949 x y
       grind)
    | exact superpose eq949 eq16
    | (have j1 := eq949 x y
       grind)
    | exact resolve eq16 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq4817 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4002
       have i₂ := eq2679 y x
       grind)
    | exact superpose eq2679 eq4002
    | (have j1 := eq2679 x y
       grind)
    | exact resolve eq4002 eq2679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2679 eq4002
  have eq4818 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq4817
  have eq4819 : (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq4818
  have eq4863 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq65 (M.op y y)
       have i₂ := eq4819
       grind)
    | exact superpose eq4819 eq65
    | exact resolve eq65 eq4819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4819
  have eq4917 : (σ y) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq4863
       have i₂ := eq19 y y y
       grind)
    | (have i₁ := eq4863
       have i₂ := eq19 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq19 eq4863
    | exact resolve eq4863 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4863
  have eq4935 : (σ y) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq4917
       have i₂ := eq65 (M.op x x)
       grind)
    | exact superpose eq65 eq4917
    | exact resolve eq4917 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4917
  have eq4938 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4935
       have i₂ := eq19 x x x
       grind)
    | (have i₁ := eq4935
       have i₂ := eq19 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq19 eq4935
    | exact resolve eq4935 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq4935
  have eq5138 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4938
       grind)
    | exact superpose eq4938 eq16
    | exact resolve eq16 eq4938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5139 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4938
       grind)
    | exact superpose eq4938 eq10
    | exact resolve eq10 eq4938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4938
  have eq5223 : x = y := by
    first
    | (have i₁ := eq5139
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5139
    | exact resolve eq5139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5139
  have eq5224 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5138
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq5138
    | exact resolve eq5138 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq5138
  have eq5227 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5224
       have i₂ := eq5223
       grind)
    | exact superpose eq5223 eq5224
    | exact resolve eq5224 eq5223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5223 eq5224
  have eq5228 : False := by grind
  exact eq5228

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_x_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq61 X0 X0 X0
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq342 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq339 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq339 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq339 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq357 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq342 (σ X0)
       grind)
    | exact superpose eq342 eq15
    | exact resolve eq15 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq342 X0
       grind)
    | exact superpose eq342 eq357
    | exact resolve eq357 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq357
  have eq428 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       have j1 := eq430 X0 X1
       grind)
    | (have r₁ := eq428 X0 X1
       have r₂ := eq430 X0 X1
       grind)
    | exact resolve eq428 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq1060 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq431 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq431
    | exact resolve eq431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1071 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq431 X1 (σ X0)
       grind)
    | exact superpose eq431 eq15
    | (have j1 := eq431 X1 (σ X0)
       grind)
    | exact resolve eq15 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq1111 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1060 X1 (τ X0)
       grind)
    | exact superpose eq1060 eq17
    | (have j1 := eq1060 X1 (τ X0)
       grind)
    | exact resolve eq17 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1060
  have eq1312 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1111 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1111
    | exact resolve eq1111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1380 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1312 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1312
    | (have j0 := eq1312 X0 X1
       grind)
    | exact resolve eq1312 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312
  have eq1886 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1071 x y
       grind)
    | exact superpose eq1071 eq16
    | (have j1 := eq1071 x y
       grind)
    | exact resolve eq16 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1991 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1886
       have i₂ := eq1380 x y
       grind)
    | exact superpose eq1380 eq1886
    | (have j1 := eq1380 (σ x) (σ y)
       grind)
    | (have r₁ := eq1886
       have r₂ := eq1380 x y
       grind)
    | exact resolve eq1886 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq1992 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1991
  have eq1999 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq62 y x x
       have i₂ := eq1992
       grind)
    | exact superpose eq1992 eq62
    | exact resolve eq62 eq1992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2052 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1999 x
       have i₂ := eq1992
       grind)
    | exact superpose eq1992 eq1999
    | exact resolve eq1999 eq1992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992 eq1999
  have eq2067 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq2052
  have eq2079 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (σ y) (σ x)
       have i₂ := eq2067
       grind)
    | exact superpose eq2067 eq61
    | exact resolve eq61 eq2067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2067
  have eq2200 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2079 (M.op x (σ y))
       have i₂ := eq2079 x
       grind)
    | exact superpose eq2079 eq2079
    | exact resolve eq2079 eq2079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079
  have eq2224 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2200
  have eq2227 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2224
       have i₂ := eq376 y
       grind)
    | exact superpose eq376 eq2224
    | exact resolve eq2224 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq2224
  have eq2238 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq430 y X0
       have i₂ := eq2227
       grind)
    | exact superpose eq2227 eq430
    | (have j0 := eq430 y X0
       grind)
    | (have r₁ := eq430 y x
       have r₂ := eq2227
       grind)
    | exact resolve eq430 eq2227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227
  have eq2266 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq2238 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238
  have eq2269 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq2266 X0
       have j1 := eq430 y X0
       grind)
    | (have r₁ := eq2266 X0
       have r₂ := eq430 y x
       grind)
    | exact resolve eq2266 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq2266
  have eq2278 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq2269 (σ X0)
       grind)
    | exact superpose eq2269 eq15
    | exact resolve eq15 eq2269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2392 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2278 x
       grind)
    | exact superpose eq2278 eq16
    | exact resolve eq16 eq2278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2278
  have eq2491 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2392
       have i₂ := eq1380 x y
       grind)
    | exact superpose eq1380 eq2392
    | (have j1 := eq1380 x y
       grind)
    | (have r₁ := eq2392
       have r₂ := eq1380 x y
       grind)
    | exact resolve eq2392 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380
  have eq2492 : y = (M.op y x) := by grind
  clear eq2491
  have eq2499 : ∀ X0 : G, y = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq61 X0 y x
       have i₂ := eq2492
       grind)
    | exact superpose eq2492 eq61
    | exact resolve eq61 eq2492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq2492
  have eq2511 : y = (M.op y y) := by
    first
    | (have i₁ := eq2499 (M.op x y)
       have i₂ := eq2499 x
       grind)
    | exact superpose eq2499 eq2499
    | exact resolve eq2499 eq2499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2499
  have eq2536 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq92 y x
       have i₂ := eq2511
       grind)
    | exact superpose eq2511 eq92
    | (have r₁ := eq92 y x
       have r₂ := eq2511
       grind)
    | exact resolve eq92 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq2511
  have eq2571 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq2536 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2536
  have eq2644 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2392
       have i₂ := eq2571 x
       grind)
    | exact superpose eq2571 eq2392
    | exact resolve eq2392 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2392 eq2571
  have eq2647 : False := by grind
  exact eq2647

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then m(Y,X) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_pyx_pyy_Equation2164 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq19 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq18 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq21 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq23 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : (M.op x y) = (M.op x y) := by grind
  have eq25 : (M.op x y) = (M.op x y) := by grind
  clear eq24
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq27 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq26
  have eq28 : (σ x) = (σ x) := by grind
  have eq29 : (σ x) = (σ x) := by grind
  clear eq28
  have eq30 : (σ y) = (σ y) := by grind
  have eq31 : (σ y) = (σ y) := by grind
  clear eq30
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq33 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq32
  have eq34 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq35 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq19
    | (have j1 := eq20 X0
       grind)
    | exact resolve eq19 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20
  have eq36 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq23 eq22
    | (have j1 := eq23 X0
       grind)
    | exact resolve eq22 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq29
       grind)
    | exact superpose eq29 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq41 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq31
       grind)
    | exact superpose eq31 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq42 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq39
       grind)
    | exact superpose eq39 eq25
    | exact resolve eq25 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq39
  have eq43 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq42
       have i₂ := eq41
       grind)
    | exact superpose eq41 eq42
    | exact resolve eq42 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq42
  have eq47 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq49 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (k X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq65 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (τ X0) X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq47
    | exact resolve eq47 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq27 eq47
    | (have j0 := eq47 (M.op x y) X0
       grind)
    | exact resolve eq47 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq84 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq27 eq69
    | (have j0 := eq69 (M.op x y)
       grind)
    | exact resolve eq69 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq89 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq116 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) X1) (k X0 X1)) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) X1) (k X0 X1)) = X1 ∨ (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    grind
  clear eq116
  have eq165 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    grind
  have eq168 : ∀ X0 : G, (τ (σ y)) = (M.op (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq43 eq49
    | exact resolve eq49 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (τ (σ x)) = (M.op (M.op X0 (τ (σ x))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq43 eq49
    | exact resolve eq49 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq183 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq188 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    grind
  clear eq183
  have eq206 : (τ (σ y)) = (M.op (M.op x y) (k (τ (σ y)) (τ (σ y)))) := by grind
  clear eq168
  have eq274 : ∀ X1 : G, (M.op x y) = (M.op (τ (σ x)) (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq175 eq49
    | exact resolve eq49 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq175
  have eq326 : (M.op x y) = (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) := by grind
  clear eq274
  have eq336 : (M.op x y) ≠ (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (k (M.op x y) (M.op x y)) (τ (σ x))) := by
    first
    | exact superpose eq326 eq13
    | (have j0 := eq13 (τ (σ x)) (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq13 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq341 : (M.op x y) ≠ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (k (M.op x y) (M.op x y)) (τ (σ x))) := by grind
  clear eq336
  have eq342 : (M.op x y) = (k (k (M.op x y) (M.op x y)) (τ (σ x))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq341
       have r₂ := eq188 (M.op x y)
       grind)
    | exact resolve eq341 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq368 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X1 (τ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq65
    | exact resolve eq65 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq860 : (τ (σ y)) ≠ (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (k (τ (σ y)) (τ (σ y))) (M.op x y)) := by
    first
    | exact superpose eq206 eq89
    | (have j0 := eq89 (M.op x y) (k (τ (σ y)) (τ (σ y)))
       grind)
    | exact resolve eq89 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq206
  have eq863 : (τ (σ y)) = (k (k (τ (σ y)) (τ (σ y))) (M.op x y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have r₁ := eq860
       have r₂ := eq188 (τ (σ y))
       grind)
    | exact resolve eq860 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq1070 : (σ (M.op x y)) = (k (σ (k (M.op x y) (M.op x y))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq342 eq15
    | exact resolve eq15 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq1071 : (σ (M.op x y)) = (k (σ (k (M.op x y) (M.op x y))) (σ x)) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1070
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq1070
    | exact resolve eq1070 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1073 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1071
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq1071
    | exact resolve eq1071 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1074 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27 eq1073
    | exact resolve eq1073 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1232 : ∀ X0 X3 : G, (k X3 X0) = (M.op X0 (k (k X3 X0) (k X3 X0))) ∨ (M.op X0 X3) = (k X3 X3) ∨ X0 = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq55 (k X3 X0) (M.op x x) X0
       have i₂ := eq122 X3 X0 x x
       grind)
    | exact superpose eq122 eq55
    | (have j1 := eq122 X3 X0 x X3
       grind)
    | exact resolve eq55 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq122
  have eq1774 : (σ (τ (σ y))) = (k (σ (k (τ (σ y)) (τ (σ y)))) (σ (M.op x y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq863 eq15
    | exact resolve eq15 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq1791 : (σ (τ (σ y))) = (k (σ (k (τ (σ y)) (τ (σ y)))) (σ (M.op x y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq27 eq1774
    | exact resolve eq1774 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774
  have eq1795 : (σ (τ (σ y))) = (k (k (σ (τ (σ y))) (σ (τ (σ y)))) (σ (M.op x y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq1791
       have i₂ := eq15 (τ sF5) (τ sF5)
       grind)
    | exact superpose eq15 eq1791
    | exact resolve eq1791 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1791
  have eq1796 : (σ y) = (k (k (σ y) (σ y)) (σ (M.op x y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq1795
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq1795
    | exact resolve eq1795 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq8871 : (σ y) = (M.op (σ (M.op x y)) (k (σ y) (σ y))) ∨ (M.op (σ (M.op x y)) (k (σ y) (σ y))) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq1796 eq1232
    | (have j0 := eq1232 (σ (M.op x y)) (k (σ y) (σ y))
       grind)
    | exact resolve eq1232 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq8872 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1074 eq1232
    | (have j0 := eq1232 (σ x) (k (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq1232 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq1232
  have eq9006 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq8872
       have i₂ := eq188 sF3
       grind)
    | exact superpose eq188 eq8872
    | exact resolve eq8872 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8872
  have eq9007 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by grind
  clear eq9006
  have eq9008 : (σ y) = (M.op (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq8871
       have i₂ := eq188 sF5
       grind)
    | exact superpose eq188 eq8871
    | exact resolve eq8871 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8871
  have eq9009 : (σ y) = (M.op (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by grind
  clear eq9008
  have eq10441 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq9007 eq53
    | exact resolve eq53 eq9007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq13968 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq9009 eq10441
    | exact resolve eq10441 eq9009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10441
  have eq13992 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq9009 eq165
    | exact resolve eq165 eq9009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq9009
  have eq14027 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq33 eq13968
    | exact resolve eq13968 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13968
  have eq14028 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq14027
       have r₂ := eq34
       grind)
    | exact resolve eq14027 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14027
  have eq505183 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14028 eq188
    | exact resolve eq188 eq14028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14028
  have eq505192 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq505183 eq36
    | exact resolve eq36 eq505183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505183
  have eq505193 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq505192
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq505192
    | exact resolve eq505192 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505192
  have eq505195 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq505193
    | exact resolve eq505193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505193
  have eq505199 : (σ x) = (σ (k (M.op x y) (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq505195 eq36
    | exact resolve eq36 eq505195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505195
  have eq505200 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq505199
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq505199
    | exact resolve eq505199 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505199
  have eq505202 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq505200
    | exact resolve eq505200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505200
  have eq505203 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq505202
  have eq505249 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq505203 eq188
    | exact resolve eq188 eq505203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505203
  have eq505274 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq505249
  have eq505321 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq505274 eq13992
    | exact resolve eq13992 eq505274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13992
  have eq505589 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq505274 eq188
    | exact resolve eq188 eq505274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505274
  have eq506076 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by grind
  clear eq505321
  have eq506144 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq33 eq506076
    | exact resolve eq506076 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506076
  have eq506166 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq506144
       have r₂ := eq34
       grind)
    | exact resolve eq506144 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506144
  have eq506176 : (k (M.op x y) (M.op x y)) = (τ (k (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq505589 eq84
    | exact resolve eq84 eq505589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq506220 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq505589
  have eq506227 : (k (M.op x y) (M.op x y)) = (k (τ (k (σ y) (σ y))) (τ (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq506176
       have i₂ := eq368 (k sF5 sF5) (k sF5 sF5)
       grind)
    | exact superpose eq368 eq506176
    | exact resolve eq506176 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506176
  have eq506235 : (k (M.op x y) (M.op x y)) = (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq506227
       have i₂ := eq368 sF5 sF5
       grind)
    | exact superpose eq368 eq506227
    | exact resolve eq506227 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq506227
  have eq506241 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq506235
       have i₂ := eq188 (τ sF5)
       grind)
    | exact superpose eq188 eq506235
    | exact resolve eq506235 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506235
  have eq506362 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq506241 eq36
    | exact resolve eq36 eq506241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506241
  have eq506371 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq506362
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq506362
    | exact resolve eq506362 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506362
  have eq506375 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq506371
    | exact resolve eq506371 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506371
  have eq506421 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq506375 eq9007
    | exact resolve eq9007 eq506375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9007 eq506375
  have eq507232 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq33 eq506421
    | exact resolve eq506421 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506421
  have eq507252 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq507232
       have r₂ := eq34
       grind)
    | exact resolve eq507232 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507232
  have eq510067 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq506166 eq15
    | exact resolve eq15 eq506166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506166
  have eq510076 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq510067
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq510067
    | exact resolve eq510067 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510067
  have eq510102 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq510076
    | exact resolve eq510076 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510076
  have eq510103 : (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq510102
  have eq521177 : (σ x) = (σ (k (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq507252 eq36
    | exact resolve eq36 eq507252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq507252
  have eq521178 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq521177
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq521177
    | exact resolve eq521177 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521177
  have eq521181 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq521178
    | exact resolve eq521178 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq521178
  have eq521182 : (σ x) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq510103 eq521181
    | exact resolve eq521181 eq510103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521181
  have eq521183 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq521182
       have i₂ := eq188 sF5
       grind)
    | exact superpose eq188 eq521182
    | exact resolve eq521182 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521182
  have eq521184 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq521183
  have eq521185 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq510103 eq521184
    | exact resolve eq521184 eq510103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510103 eq521184
  have eq521267 : (σ y) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq521185 eq188
    | exact resolve eq188 eq521185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521185
  have eq521732 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq521267
       have i₂ := eq188 sF4
       grind)
    | exact superpose eq188 eq521267
    | exact resolve eq521267 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq521267
  have eq521733 : (σ x) = (σ y) := by grind
  clear eq521732
  have eq521746 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq521733 eq33
    | exact resolve eq33 eq521733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq522752 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq521733 eq506220
    | exact resolve eq506220 eq521733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506220 eq521733
  have eq522768 : (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq522752
  have eq523250 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq521746
  have eq524145 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq523250 eq34
    | exact resolve eq34 eq523250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq523250
  have eq524680 : False := by grind
  exact eq524680

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_y_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
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
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
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
  have eq56 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq37
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq100 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq100
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq114
    | exact resolve eq114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq211 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op (M.op (M.op x y) X0) X1) (M.op x X0)) X0) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq223 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op y X0)) = X0 := by
    intro X0
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq416 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq53 X1 x x X0
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq462 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq240 eq54
    | exact resolve eq54 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq473 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X3)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 X3 X1 X2 (M.op (M.op X0 x) (M.op X0 (M.op (M.op X1 X2) X3)))
       have i₂ := eq54 (M.op (M.op X1 X2) X3) X0 x
       grind)
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X4) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq57 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq57 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq735 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq94
  have eq749 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq735 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq751 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq749 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq749
    | (have j0 := eq749 X0
       grind)
    | exact resolve eq749 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq1109 : y = (M.op (M.op x y) (M.op (M.op (M.op x y) x) y)) := by
    first
    | (have i₁ := eq214 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq214
    | (have j0 := eq214 x y
       grind)
    | exact resolve eq214 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq1246 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y))) := by
    first
    | exact superpose eq27 eq223
    | (have j0 := eq223 (σ x) (σ y)
       grind)
    | exact resolve eq223 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq1643 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq410 X0 (M.op X1 x) (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq410
    | exact resolve eq410 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq1867 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq417 X1 X0
       grind)
    | exact superpose eq417 eq14
    | exact resolve eq14 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1957 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq2943 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (M.op (σ x) X0) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq462 eq473
    | exact resolve eq473 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq473
  have eq2971 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2943 X0
       have i₂ := eq417 sF3 (M.op sF2 X0)
       grind)
    | exact superpose eq417 eq2943
    | exact resolve eq2943 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq2943
  have eq5555 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq2971 eq446
    | exact resolve eq446 eq2971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2971
  have eq5740 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5555 eq56
    | exact resolve eq56 eq5555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq6680 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq683 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0 X0 X1
       grind)
    | exact superpose eq54 eq683
    | exact resolve eq683 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq6691 : (M.op y y) = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1109 eq683
    | exact resolve eq683 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq6699 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1246 eq683
    | exact resolve eq683 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq1246
  have eq6800 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6680 X0 X1
       have i₂ := eq1867 X0 X0
       grind)
    | exact superpose eq1867 eq6680
    | exact resolve eq6680 eq1867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6680
  have eq6920 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x y) (M.op x X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq213 x (M.op sF0 sF0)
       have i₂ := eq6800 sF0 x
       grind)
    | exact superpose eq6800 eq213
    | exact resolve eq213 eq6800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq6930 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq242 X0 (M.op (M.op sF2 X0) (M.op sF2 X0))
       have i₂ := eq6800 (M.op sF2 X0) sF3
       grind)
    | exact superpose eq6800 eq242
    | exact resolve eq242 eq6800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq6937 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq446 X1 X0 (M.op X0 X0)
       have i₂ := eq6800 X0 X1
       grind)
    | exact superpose eq6800 eq446
    | exact resolve eq446 eq6800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6800
  have eq8195 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6930 (M.op sF2 (M.op x sF2))
       have i₂ := eq1643 sF2 x
       grind)
    | exact superpose eq1643 eq6930
    | exact resolve eq6930 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643
  have eq15889 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq662 X1 (M.op X0 X2) x x (M.op X0 X1)
       have i₂ := eq658 (M.op (M.op (M.op (M.op X0 X2) x) X1) x) X0 X2 X1
       grind)
    | exact superpose eq658 eq662
    | exact resolve eq662 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq662
  have eq16632 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq446 (M.op X1 X0) X1 X0
       have i₂ := eq15889 X1 X0 (M.op X1 X0)
       grind)
    | exact superpose eq15889 eq446
    | exact resolve eq446 eq15889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq15889
  have eq76947 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76957 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq76947
    | exact resolve eq76947 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76947
  have eq76968 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq76957
       have r₂ := eq28
       grind)
    | exact resolve eq76957 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76957
  have eq76971 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq76968 eq416
    | exact resolve eq416 eq76968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76968
  have eq77119 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6699 eq76971
    | exact resolve eq76971 eq6699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76971
  have eq77743 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77119 eq6937
    | exact resolve eq6937 eq77119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77119
  have eq77748 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq77743
  have eq77791 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77748 eq1957
    | exact resolve eq1957 eq77748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77748
  have eq77902 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq77791
    | exact resolve eq77791 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77791
  have eq78529 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77902 eq115
    | exact resolve eq115 eq77902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq77902
  have eq78546 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq78529
  have eq78548 : y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq78546
       have r₂ := eq28
       grind)
    | exact resolve eq78546 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78546
  have eq78962 : x = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq414 x
       have i₂ := eq78548
       grind)
    | exact superpose eq78548 eq414
    | exact resolve eq414 eq78548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq78548
  have eq79111 : y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq6691 eq78962
    | exact resolve eq78962 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6691 eq78962
  have eq79738 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq6937 x x
       have i₂ := eq79111
       grind)
    | exact superpose eq79111 eq6937
    | exact resolve eq6937 eq79111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79111
  have eq79743 : x = (M.op y y) := by grind
  clear eq79738
  have eq79787 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1957 y
       have i₂ := eq79743
       grind)
    | exact superpose eq79743 eq1957
    | exact resolve eq1957 eq79743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq79886 : y = (M.op x x) := by
    first
    | (have i₁ := eq1867 y y
       have i₂ := eq79743
       grind)
    | exact superpose eq79743 eq1867
    | exact resolve eq1867 eq79743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1867 eq79743
  have eq79898 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq79787
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79787
    | exact resolve eq79787 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq79787
  have eq80619 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq111
       have i₂ := eq79886
       grind)
    | exact superpose eq79886 eq111
    | exact resolve eq111 eq79886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq79886
  have eq80804 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq80619
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq80619
    | exact resolve eq80619 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80619
  have eq80975 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq79898
       grind)
    | exact superpose eq79898 eq73
    | exact resolve eq73 eq79898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79898
  have eq81011 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq80975
    | exact resolve eq80975 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq80975
  have eq81080 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq81011 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq81011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81090 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq81080
    | exact resolve eq81080 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81080
  have eq81101 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq81090
       have r₂ := eq28
       grind)
    | exact resolve eq81090 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81090
  have eq87397 : (τ (σ y)) = (k x x) ∨ x = y := by
    first
    | exact superpose eq80804 eq50
    | exact resolve eq50 eq80804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq80804
  have eq87437 : y = (k x x) ∨ x = y := by
    first
    | exact superpose eq30 eq87397
    | exact resolve eq87397 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq87397
  have eq88731 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq751 x
       have i₂ := eq87437
       grind)
    | exact superpose eq87437 eq751
    | (have j0 := eq751 x
       grind)
    | exact resolve eq751 eq87437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751 eq87437
  have eq88764 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq88731
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq88731
    | exact resolve eq88731 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq88731
  have eq88783 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq81011 eq88764
    | exact resolve eq88764 eq81011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88764
  have eq88794 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq88783
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq88783
    | exact resolve eq88783 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88783
  have eq88796 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq88794
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq88794
    | exact resolve eq88794 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88794
  have eq88798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27 eq88796
    | exact resolve eq88796 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88796
  have eq88800 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq88798
       have r₂ := eq28
       grind)
    | exact resolve eq88798 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88798
  have eq88801 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq88800
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq88800
    | exact resolve eq88800 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88800
  have eq89010 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ x = y := by
    first
    | exact superpose eq88801 eq8195
    | exact resolve eq8195 eq88801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8195 eq88801
  have eq89140 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq5555 eq89010
    | exact resolve eq89010 eq5555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89010
  have eq99685 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq81101 eq416
    | exact resolve eq416 eq81101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq99715 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq81101 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq81101
       grind)
    | exact resolve eq12 eq81101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81101
  have eq99824 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq99715
  have eq99825 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq99824
  have eq99838 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq81011 eq99825
    | exact resolve eq99825 eq81011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99825
  have eq99843 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6699 eq99685
    | exact resolve eq99685 eq6699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99685
  have eq100391 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq99838
  have eq100511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq81011 eq100391
    | exact resolve eq100391 eq81011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81011 eq100391
  have eq100520 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq100511
    | exact resolve eq100511 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq100511
  have eq100521 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq100520
       have r₂ := eq28
       grind)
    | exact resolve eq100520 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100520
  have eq100523 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq100521 eq29
    | exact resolve eq29 eq100521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq100529 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ (M.op x y)) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq100521 eq52
    | exact resolve eq52 eq100521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq100635 : (M.op (σ y) (σ y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq100521 eq5555
    | exact resolve eq5555 eq100521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5555
  have eq100638 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq100521 eq6699
    | exact resolve eq6699 eq100521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6699
  have eq100642 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq100521 eq6930
    | exact resolve eq6930 eq100521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6930
  have eq100726 : x = (M.op x y) := by
    first
    | exact superpose eq31 eq100523
    | exact resolve eq100523 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq100523
  have eq100913 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x (M.op x X0)) X0) := by
    intro X0
    first
    | exact superpose eq100726 eq6920
    | exact resolve eq6920 eq100726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6920
  have eq100969 : ∀ X0 : G, (M.op x X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq100913 X0
       have i₂ := eq16632 X0 x
       grind)
    | exact superpose eq16632 eq100913
    | exact resolve eq100913 eq16632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16632 eq100913
  have eq106174 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ x = y := by
    first
    | exact superpose eq89140 eq100969
    | exact resolve eq100969 eq89140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89140
  have eq106442 : ∀ X0 : G, (M.op (M.op x X0) (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq6937 X0 x
       have i₂ := eq100969 X0
       grind)
    | (have i₁ := eq6937 X0 X0
       have i₂ := eq100969 X0
       grind)
    | exact superpose eq100969 eq6937
    | exact resolve eq6937 eq100969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6937
  have eq106848 : (σ y) = (M.op (M.op x (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5740
       have i₂ := eq100969 sF3
       grind)
    | exact superpose eq100969 eq5740
    | exact resolve eq5740 eq100969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5740
  have eq107084 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq106442 X0
       have i₂ := eq100969 (M.op x X0)
       grind)
    | exact superpose eq100969 eq106442
    | exact resolve eq106442 eq100969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106442
  have eq122302 : (M.op (M.op x y) (M.op x (σ (M.op x y)))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op x (σ (M.op x y))))) (M.op x (σ (M.op x y)))) := by
    first
    | exact superpose eq211 eq100529
    | exact resolve eq100529 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq100529
  have eq122527 : (M.op x (M.op x (σ (M.op x y)))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x (M.op x (σ (M.op x y))))) (M.op x (σ (M.op x y)))) := by
    first
    | exact superpose eq100726 eq122302
    | exact resolve eq122302 eq100726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100726 eq122302
  have eq122587 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op x (σ (M.op x y)))) := by
    first
    | (have i₁ := eq122527
       have i₂ := eq107084 sF1
       grind)
    | exact superpose eq107084 eq122527
    | exact resolve eq122527 eq107084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107084 eq122527
  have eq124327 : (M.op x (σ y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq100635
       have i₂ := eq100969 sF3
       grind)
    | exact superpose eq100969 eq100635
    | exact resolve eq100635 eq100969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100635
  have eq124329 : (M.op x (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq100638
       have i₂ := eq100969 sF3
       grind)
    | exact superpose eq100969 eq100638
    | exact resolve eq100638 eq100969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100638
  have eq134577 : (σ x) = (M.op x (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq99843
       have i₂ := eq100969 sF3
       grind)
    | exact superpose eq100969 eq99843
    | exact resolve eq99843 eq100969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99843
  have eq134578 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq100521 eq134577
    | exact resolve eq134577 eq100521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134577
  have eq134579 : (σ y) = (M.op x (σ x)) ∨ (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq134578
       have i₂ := eq100969 sF2
       grind)
    | exact superpose eq100969 eq134578
    | exact resolve eq134578 eq100969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100969 eq134578
  have eq134580 : (σ y) = (M.op x (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq100521 eq134579
    | exact resolve eq134579 eq100521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134579
  have eq135019 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq134580 eq122587
    | exact resolve eq122587 eq134580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122587 eq134580
  have eq135274 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq124329 eq135019
    | exact resolve eq135019 eq124329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124329 eq135019
  have eq135275 : (σ (M.op x y)) = (M.op x (σ y)) := by grind
  clear eq135274
  have eq135295 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq135275 eq106174
    | exact resolve eq106174 eq135275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106174
  have eq135296 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq135275 eq106848
    | exact resolve eq106848 eq135275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106848
  have eq135541 : x = y := by
    first
    | (have r₁ := eq135295
       have r₂ := eq28
       grind)
    | exact resolve eq135295 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135295
  have eq135577 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq135541
       grind)
    | exact superpose eq135541 eq25
    | exact resolve eq25 eq135541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq135541
  have eq135920 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq135577
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq135577
    | exact resolve eq135577 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq135577
  have eq136027 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq100521 eq135920
    | exact resolve eq135920 eq100521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100521 eq135920
  have eq136675 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq136027 eq135296
    | exact resolve eq135296 eq136027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135296 eq136027
  have eq136694 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq136675 eq100642
    | exact resolve eq100642 eq136675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100642 eq136675
  have eq136862 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq124327 eq136694
    | exact resolve eq136694 eq124327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124327 eq136694
  have eq136880 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq135275 eq136862
    | exact resolve eq136862 eq135275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135275 eq136862
  have eq136886 : False := by grind
  exact eq136886

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq56 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq56 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq56 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq57 (σ X0)
       grind)
    | exact superpose eq57 eq15
    | exact resolve eq15 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq59
    | exact resolve eq59 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq59
  have eq83 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq89
  have eq398 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq95 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq432 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq398 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq438 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq432 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq432 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq432 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq448 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq438 X0 X1
       have j1 := eq83 X0 (σ X1)
       grind)
    | (have r₁ := eq438 X0 X1
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq438 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq438
  have eq456 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq448
    | (have j0 := eq448 X0 X1
       grind)
    | exact resolve eq448 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq457 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq456 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq462 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq457 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq457
    | exact resolve eq457 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq457 x y
       grind)
    | exact superpose eq457 eq16
    | exact resolve eq16 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq576 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq462 X0 (τ X1)
       grind)
    | exact superpose eq462 eq17
    | exact resolve eq17 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq462
  have eq590 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq576 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq576
    | exact resolve eq576 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq597 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq590 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq590
    | exact resolve eq590 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq609 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq473
       have i₂ := eq597 x y
       grind)
    | exact superpose eq597 eq473
    | exact resolve eq473 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473 eq597
  have eq610 : False := by grind
  exact eq610

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxx_x_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq75 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (k y x) := by
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
  have eq76 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112
    | exact resolve eq112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq170 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq192 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq234 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op x X0) y) X1) (M.op x y)) y) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op x X0) (M.op (M.op (M.op x x) x) X0) X2
       have i₂ := eq52 x x x X0
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq52 X1 x x X0
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq234 eq53
    | exact resolve eq53 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq239 eq53
    | exact resolve eq53 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq468 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op (M.op x X0) y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : ∀ X0 : G, y = (M.op (M.op (M.op X0 x) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op (M.op X0 x) (M.op X0 x))
       have i₂ := eq53 x X0 x
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq493 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq55 (M.op (M.op x x) (M.op x sF2))
       have i₂ := eq53 sF2 x x
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : ∀ X0 X1 X2 X4 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X4) (M.op X1 X2)) X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq56 X2 X1 (M.op (M.op X0 x) (M.op X0 X1)) X4
       have i₂ := eq53 X1 X0 x
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op (M.op X0 X2) X5) (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq56 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0) X5
       have i₂ := eq52 X1 x x X0
       grind)
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq633 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X2) X1) X3) X1) = (M.op (M.op (M.op (M.op X0 X1) X4) (M.op (M.op (M.op (M.op X0 X2) X1) X3) X1)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 X1 (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1) X4
       have i₂ := eq56 X1 X0 X2 X3
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X3)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X3 X1 X2 (M.op (M.op X0 x) (M.op X0 (M.op (M.op X1 X2) X3)))
       have i₂ := eq53 (M.op (M.op X1 X2) X3) X0 x
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4) X1) X5) (M.op X0 X1)) X1) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56 X0 (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X2 X3
       have i₂ := eq56 X0 X1 X2 X3
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X4) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq56 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq733 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq93 X0 X0
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq93 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq93 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq93 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq745 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq744 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq747 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq733 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq749 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq747 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq747 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq747 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq1618 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq408 X0 (M.op X1 x) (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq408
    | exact resolve eq408 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq1840 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq415 X1 X0
       grind)
    | exact superpose eq415 eq14
    | exact resolve eq14 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1918 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1840 X1 (M.op X0 X0)
       have i₂ := eq1840 X0 X0
       grind)
    | exact superpose eq1840 eq1840
    | exact resolve eq1840 eq1840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2817 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y (M.op (M.op x X0) y)) y)) := by
    intro X0
    first
    | exact superpose eq456 eq468
    | exact resolve eq468 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq468
  have eq2847 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) y)) := by
    intro X0
    first
    | (have i₁ := eq2817 X0
       have i₂ := eq415 y (M.op x X0)
       grind)
    | exact superpose eq415 eq2817
    | exact resolve eq2817 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2817
  have eq2903 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (M.op (σ x) X0) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq460 eq471
    | exact resolve eq471 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq2931 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2903 X0
       have i₂ := eq415 sF3 (M.op sF2 X0)
       grind)
    | exact superpose eq415 eq2903
    | exact resolve eq2903 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq2903
  have eq5492 : (M.op y y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq2847 eq444
    | exact resolve eq444 eq2847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2847
  have eq5497 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq2931 eq444
    | exact resolve eq444 eq2931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2931
  have eq6468 : ∀ X0 X1 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 X0) (M.op X0 X3)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq681 (M.op X1 x) (M.op (M.op X0 X1) x) x
       have i₂ := eq393 X0 X1 x
       grind)
    | exact superpose eq393 eq681
    | exact resolve eq681 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq6612 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X1
       grind)
    | exact superpose eq53 eq681
    | exact resolve eq681 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq681
  have eq6731 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6612 X0 X1
       have i₂ := eq1840 X0 X0
       grind)
    | exact superpose eq1840 eq6612
    | exact resolve eq6612 eq1840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840 eq6612
  have eq6814 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq26 eq6731
    | (have j0 := eq6731 (σ x) (σ y)
       grind)
    | exact resolve eq6731 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6859 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x X0) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq236 X0 (M.op (M.op x X0) (M.op x X0))
       have i₂ := eq6731 (M.op x X0) y
       grind)
    | exact superpose eq6731 eq236
    | exact resolve eq236 eq6731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6861 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq241 X0 (M.op (M.op sF2 X0) (M.op sF2 X0))
       have i₂ := eq6731 (M.op sF2 X0) sF3
       grind)
    | exact superpose eq6731 eq241
    | exact resolve eq241 eq6731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6867 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq444 X1 X0 (M.op X0 X0)
       have i₂ := eq6731 X0 X1
       grind)
    | exact superpose eq6731 eq444
    | exact resolve eq444 eq6731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6945 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq6814 eq6731
    | exact resolve eq6731 eq6814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6814
  have eq7123 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq745 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq745
    | (have j0 := eq745 (τ X0)
       grind)
    | exact resolve eq745 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq7131 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7123 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7123
    | (have j0 := eq7123 X0
       grind)
    | exact resolve eq7123 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7123
  have eq7137 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7131 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7131
    | (have j0 := eq7131 X0
       grind)
    | exact resolve eq7131 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7131
  have eq8072 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 x) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq6859 (M.op x (M.op X0 x))
       have i₂ := eq1618 x X0
       grind)
    | exact superpose eq1618 eq6859
    | exact resolve eq6859 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6859
  have eq8134 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6861 (M.op sF2 (M.op x sF2))
       have i₂ := eq1618 sF2 x
       grind)
    | exact superpose eq1618 eq6861
    | exact resolve eq6861 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618 eq6861
  have eq14260 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq170 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq170
    | (have j0 := eq170 x
       grind)
    | exact resolve eq170 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq14333 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq14260
  have eq14338 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14333
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq14333
    | exact resolve eq14333 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq14333
  have eq14346 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq14338
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq14338 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14338
  have eq14352 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq14346 eq49
    | exact resolve eq49 eq14346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq14346
  have eq14470 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq192 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq192
    | (have j0 := eq192 y
       grind)
    | exact resolve eq192 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq14530 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq14470
  have eq14534 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq14530
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq14530
    | exact resolve eq14530 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq14530
  have eq14544 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq14534
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq14534 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14534
  have eq14551 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq14544 eq87
    | exact resolve eq87 eq14544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq14544
  have eq16197 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq660 X1 (M.op X0 X2) x x (M.op X0 X1)
       have i₂ := eq656 (M.op (M.op (M.op (M.op X0 X2) x) X1) x) X0 X2 X1
       grind)
    | exact superpose eq656 eq660
    | exact resolve eq660 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656 eq660
  have eq16947 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq444 (M.op X1 X0) X1 X0
       have i₂ := eq16197 X1 X0 (M.op X1 X0)
       grind)
    | exact superpose eq16197 eq444
    | exact resolve eq444 eq16197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16197
  have eq24111 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) (M.op x y)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq236 sF0 (M.op (M.op (M.op (M.op x x) sF0) x) sF0)
       have i₂ := eq633 x sF0 x x y
       grind)
    | exact superpose eq633 eq236
    | exact resolve eq236 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq24116 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq241 sF4 (M.op (M.op (M.op (M.op sF2 x) sF4) x) sF4)
       have i₂ := eq633 sF2 sF4 x x sF3
       grind)
    | exact superpose eq633 eq241
    | exact resolve eq241 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq633
  have eq24887 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1 x x (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq609 (M.op (M.op (M.op X0 x) X1) x) (M.op X0 X1) (M.op X0 X1) X1
       grind)
    | exact superpose eq609 eq658
    | exact resolve eq658 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq658
  have eq51833 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51842 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq51833
    | exact resolve eq51833 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51833
  have eq51847 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq51842
       have r₂ := eq27
       grind)
    | exact resolve eq51842 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51842
  have eq51849 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq51847
    | exact resolve eq51847 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51847
  have eq51851 : (τ (σ x)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq51849 eq14352
    | exact resolve eq14352 eq51849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51849
  have eq52007 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq51851
    | exact resolve eq51851 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51851
  have eq52008 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq7137 x
       grind)
    | (have r₁ := eq52007
       have r₂ := eq7137 x
       grind)
    | exact resolve eq52007 eq7137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52007
  have eq52035 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq489 x
       have i₂ := eq52008
       grind)
    | exact superpose eq52008 eq489
    | exact resolve eq489 eq52008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq52036 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq52008
       grind)
    | exact superpose eq52008 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq52008
       grind)
    | exact resolve eq13 eq52008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52145 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq52036 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52036
  have eq52155 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52035
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52035
    | exact resolve eq52035 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq52035
  have eq54622 : ∀ X0 : G, (k (M.op X0 X0) x) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq52145 (M.op X0 X0)
       have i₂ := eq6867 X0 X0
       grind)
    | exact superpose eq6867 eq52145
    | exact resolve eq52145 eq6867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52145
  have eq59855 : x = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54622 x
       have i₂ := eq52008
       grind)
    | exact superpose eq52008 eq54622
    | exact resolve eq54622 eq52008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52008
  have eq59857 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq52155 eq54622
    | exact resolve eq54622 eq52155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52155 eq54622
  have eq59870 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq59857
  have eq59872 : x = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq59855
  have eq59905 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq59870
       grind)
    | exact superpose eq59870 eq72
    | exact resolve eq72 eq59870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq59870
  have eq59938 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq59905
    | exact resolve eq59905 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59905
  have eq60079 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq749 x X0
       have i₂ := eq59872
       grind)
    | exact superpose eq59872 eq749
    | (have j0 := eq749 x X0
       grind)
    | exact resolve eq749 eq59872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq60089 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq743 x x
       have i₂ := eq59872
       grind)
    | exact superpose eq59872 eq743
    | (have j0 := eq743 x x
       grind)
    | exact resolve eq743 eq59872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59872
  have eq60090 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq60089
  have eq60091 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq60090
  have eq60101 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq60079 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60079
  have eq60107 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq60091
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq60091
    | exact resolve eq60091 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60091
  have eq60116 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq60101 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq60101
    | (have j0 := eq60101 X0
       grind)
    | exact resolve eq60101 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60101
  have eq60205 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60107 eq8134
    | exact resolve eq8134 eq60107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8134 eq60107
  have eq60330 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5497 eq60205
    | exact resolve eq60205 eq5497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5497 eq60205
  have eq68049 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60116 eq59938
    | exact resolve eq59938 eq60116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59938 eq60116
  have eq68068 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq68049
  have eq68126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq68068 eq60330
    | exact resolve eq60330 eq68068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60330 eq68068
  have eq68248 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq68126
  have eq68252 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq68248
       have r₂ := eq27
       grind)
    | exact resolve eq68248 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68248
  have eq68255 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq68252 eq27
    | exact resolve eq27 eq68252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68257 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq68252 eq55
    | exact resolve eq55 eq68252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq68258 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq68252 eq76
    | (have r₁ := eq76
       have r₂ := eq68252
       grind)
    | exact resolve eq76 eq68252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq68283 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq68252 eq493
    | exact resolve eq493 eq68252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493 eq68252
  have eq68364 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq68258
  have eq75306 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6945 eq68257
    | (have j0 := eq68257 (σ y)
       grind)
    | exact resolve eq68257 eq6945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6945 eq68257
  have eq75551 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq75306 eq14
    | exact resolve eq14 eq75306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75306
  have eq75704 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq75551 eq460
    | exact resolve eq460 eq75551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460 eq75551
  have eq82130 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq75704 eq1918
    | exact resolve eq1918 eq75704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1918 eq75704
  have eq86615 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq68364 eq113
    | exact resolve eq113 eq68364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq68364
  have eq86632 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq86615
  have eq86642 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq86632
       have r₂ := eq68255
       grind)
    | exact resolve eq86632 eq68255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68255 eq86632
  have eq86971 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq86642 eq14352
    | exact resolve eq14352 eq86642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86642
  have eq87200 : x = (k x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq86971
    | exact resolve eq86971 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86971
  have eq87201 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq7137 x
       grind)
    | (have r₁ := eq87200
       have r₂ := eq7137 x
       grind)
    | exact resolve eq87200 eq7137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87200
  have eq87253 : (M.op x y) = (M.op (M.op x (M.op x y)) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8072 x
       have i₂ := eq87201
       grind)
    | exact superpose eq87201 eq8072
    | exact resolve eq8072 eq87201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8072
  have eq87260 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq87201
       grind)
    | exact superpose eq87201 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq87201
       grind)
    | exact resolve eq13 eq87201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87383 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq87260 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87260
  have eq87411 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5492 eq87253
    | exact resolve eq87253 eq5492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5492 eq87253
  have eq90576 : ∀ X0 : G, (k (M.op X0 X0) x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq87383 (M.op X0 X0)
       have i₂ := eq6867 X0 X0
       grind)
    | exact superpose eq6867 eq87383
    | exact resolve eq87383 eq6867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6867 eq87383
  have eq95788 : x = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq90576 x
       have i₂ := eq87201
       grind)
    | exact superpose eq87201 eq90576
    | exact resolve eq90576 eq87201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87201 eq90576
  have eq95833 : x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq95788
  have eq96084 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq743 x x
       have i₂ := eq95833
       grind)
    | exact superpose eq95833 eq743
    | (have j0 := eq743 x x
       grind)
    | exact resolve eq743 eq95833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95833
  have eq96085 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq96084
  have eq96086 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq96085
  have eq96108 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq96086
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq96086
    | exact resolve eq96086 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96086
  have eq96239 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq96108 eq68283
    | exact resolve eq68283 eq96108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68283 eq96108
  have eq96376 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq96239
  have eq96399 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq96376
    | exact resolve eq96376 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96376
  have eq97276 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq96399 eq82130
    | exact resolve eq82130 eq96399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82130 eq96399
  have eq97391 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq97276
  have eq100638 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq97391 eq14551
    | exact resolve eq14551 eq97391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14551 eq97391
  have eq100844 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq100638
    | exact resolve eq100638 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq100638
  have eq102304 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq100844
       grind)
    | exact superpose eq100844 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq100844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100844
  have eq102322 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq102304
  have eq103175 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq87411
       have i₂ := eq102322
       grind)
    | exact superpose eq102322 eq87411
    | exact resolve eq87411 eq102322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87411 eq102322
  have eq103330 : y = (M.op x y) := by grind
  clear eq103175
  have eq103354 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq103330 eq20
    | exact resolve eq20 eq103330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq103361 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq103330 eq75
    | (have r₁ := eq75
       have r₂ := eq103330
       grind)
    | exact resolve eq75 eq103330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq103536 : y = (k y x) ∨ x = (M.op x x) := by grind
  clear eq103361
  have eq103625 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq103354
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq103354
    | exact resolve eq103354 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103354
  have eq103630 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq103625 eq26
    | exact resolve eq26 eq103625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq104694 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op (M.op x X0) y) X1) y) y) := by
    intro X0 X1
    first
    | exact superpose eq103330 eq24111
    | exact resolve eq24111 eq103330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24111
  have eq104823 : ∀ X0 : G, y = (M.op (M.op (M.op X0 x) y) y) := by
    intro X0
    first
    | (have i₁ := eq104694 y (M.op (M.op X0 x) y)
       have i₂ := eq611 x X0 y y
       grind)
    | exact superpose eq611 eq104694
    | exact resolve eq104694 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104982 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y (M.op y X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq6468 y (M.op (M.op (M.op (M.op x x) y) x) y) X0
       have i₂ := eq104694 x x
       grind)
    | exact superpose eq104694 eq6468
    | exact resolve eq6468 eq104694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6468 eq104694
  have eq105000 : ∀ X0 : G, (M.op X0 X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq104982 X0
       have i₂ := eq16947 X0 y
       grind)
    | exact superpose eq16947 eq104982
    | exact resolve eq104982 eq16947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16947 eq104982
  have eq105501 : (k x x) = (τ (M.op y (σ x))) := by
    first
    | (have i₁ := eq14352
       have i₂ := eq105000 sF2
       grind)
    | exact superpose eq105000 eq14352
    | exact resolve eq14352 eq105000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14352
  have eq106162 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X1) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq103625 eq24116
    | exact resolve eq24116 eq103625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24116
  have eq106238 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq106162 X0 (M.op (M.op sF2 X0) (M.op sF2 X0))
       have i₂ := eq6731 (M.op sF2 X0) sF4
       grind)
    | exact superpose eq6731 eq106162
    | exact resolve eq106162 eq6731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6731
  have eq106288 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq106162 sF4 (M.op (M.op x sF2) sF4)
       have i₂ := eq611 sF2 x sF4 sF4
       grind)
    | exact superpose eq611 eq106162
    | exact resolve eq106162 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611 eq106162
  have eq106852 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24887 X0 X1
       have i₂ := eq105000 (M.op X0 X1)
       grind)
    | exact superpose eq105000 eq24887
    | exact resolve eq24887 eq105000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24887
  have eq107617 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq234 eq106852
    | exact resolve eq106852 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq106852
  have eq108019 : ∀ X0 : G, (M.op (M.op x X0) y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq103330 eq107617
    | exact resolve eq107617 eq103330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103330 eq107617
  have eq117195 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq106238 eq14
    | exact resolve eq14 eq106238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106238
  have eq126987 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq117195 eq444
    | exact resolve eq444 eq117195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444 eq117195
  have eq127124 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ (M.op x y))) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq126987
       have i₂ := eq105000 sF1
       grind)
    | exact superpose eq105000 eq126987
    | exact resolve eq126987 eq105000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126987
  have eq167614 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq743 x y
       have i₂ := eq103536
       grind)
    | exact superpose eq103536 eq743
    | (have j0 := eq743 x y
       grind)
    | exact resolve eq743 eq103536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq103536
  have eq167615 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq167614
  have eq167622 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq167615
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq167615
    | exact resolve eq167615 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167615
  have eq167641 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq103625 eq167622
    | exact resolve eq167622 eq103625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167622
  have eq167658 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq167641
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq167641
    | exact resolve eq167641 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167641
  have eq167675 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq103630 eq167658
    | exact resolve eq167658 eq103630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103630 eq167658
  have eq167687 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq167675
       have r₂ := eq27
       grind)
    | exact resolve eq167675 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167675
  have eq167698 : (σ x) = (M.op y (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq167687
       have i₂ := eq105000 (σ x)
       grind)
    | exact superpose eq105000 eq167687
    | exact resolve eq167687 eq105000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167687
  have eq167706 : (σ x) = (M.op y (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq167698
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq167698
    | exact resolve eq167698 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167698
  have eq167784 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq167706 eq105501
    | exact resolve eq105501 eq167706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105501 eq167706
  have eq168042 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq167784
    | exact resolve eq167784 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq167784
  have eq168064 : x = (M.op x x) := by
    first
    | (have j1 := eq7137 x
       grind)
    | (have r₁ := eq168042
       have r₂ := eq7137 x
       grind)
    | exact resolve eq168042 eq7137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7137 eq168042
  have eq168145 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq104823 x
       have i₂ := eq168064
       grind)
    | exact superpose eq168064 eq104823
    | exact resolve eq104823 eq168064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104823
  have eq168147 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq168064
       grind)
    | exact superpose eq168064 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq168064
       grind)
    | exact resolve eq13 eq168064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168292 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq168147 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168147
  have eq168336 : y = (M.op y y) := by
    first
    | (have i₁ := eq168145
       have i₂ := eq108019 y
       grind)
    | exact superpose eq108019 eq168145
    | exact resolve eq168145 eq108019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108019 eq168145
  have eq168565 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq168336
       grind)
    | exact superpose eq168336 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq168336
       grind)
    | exact resolve eq13 eq168336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168710 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq168565 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168565
  have eq171861 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq745 x
       have i₂ := eq168292 x
       grind)
    | exact superpose eq168292 eq745
    | (have j0 := eq745 x
       grind)
    | exact resolve eq745 eq168292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168292
  have eq171883 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq171861
       have i₂ := eq168064
       grind)
    | exact superpose eq168064 eq171861
    | exact resolve eq171861 eq168064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168064 eq171861
  have eq171884 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq171883
  have eq172072 : (σ x) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq171884
       have i₂ := eq105000 (σ x)
       grind)
    | exact superpose eq105000 eq171884
    | exact resolve eq171884 eq105000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171884
  have eq172147 : (σ x) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq172072
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq172072
    | exact resolve eq172072 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq172072
  have eq172307 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq172147 eq106288
    | exact resolve eq106288 eq172147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106288 eq172147
  have eq172509 : (M.op (σ x) (σ y)) = (M.op y (σ (M.op x y))) := by
    first
    | exact superpose eq127124 eq172307
    | exact resolve eq172307 eq127124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127124 eq172307
  have eq177751 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq745 y
       have i₂ := eq168710 y
       grind)
    | exact superpose eq168710 eq745
    | (have j0 := eq745 y
       grind)
    | exact resolve eq745 eq168710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq168710
  have eq177773 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq177751
       have i₂ := eq168336
       grind)
    | exact superpose eq168336 eq177751
    | exact resolve eq177751 eq168336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168336 eq177751
  have eq177774 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq177773
  have eq177966 : (σ y) = (M.op y (σ y)) := by
    first
    | (have i₁ := eq177774
       have i₂ := eq105000 (σ y)
       grind)
    | exact superpose eq105000 eq177774
    | exact resolve eq177774 eq105000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105000 eq177774
  have eq178043 : (σ y) = (M.op y (σ y)) := by
    first
    | (have i₁ := eq177966
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq177966
    | exact resolve eq177966 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq177966
  have eq178100 : (σ (M.op x y)) = (M.op y (σ (M.op x y))) := by
    first
    | exact superpose eq103625 eq178043
    | exact resolve eq178043 eq103625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103625 eq178043
  have eq178150 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq172509 eq178100
    | exact resolve eq178100 eq172509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172509 eq178100
  have eq178195 : False := by grind
  exact eq178195

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_x_pyx_Equation2165 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq88 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq37
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq521 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq55 X1 x x X0
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq708 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq59 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1897 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq521 X1 X0
       grind)
    | exact superpose eq521 eq14
    | exact resolve eq14 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq7618 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq708 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0 X0 X1
       grind)
    | exact superpose eq56 eq708
    | exact resolve eq708 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq708
  have eq7740 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7618 X0 X1
       have i₂ := eq1897 X0 X0
       grind)
    | exact superpose eq1897 eq7618
    | exact resolve eq7618 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7618
  have eq7894 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq547 X1 X0 (M.op X0 X0)
       have i₂ := eq7740 X0 X1
       grind)
    | exact superpose eq7740 eq547
    | exact resolve eq547 eq7740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq80015 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq7740 y y
       have i₂ := eq102
       grind)
    | exact superpose eq102 eq7740
    | exact resolve eq7740 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq7740
  have eq80024 : x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq80015
       have i₂ := eq1897 x x
       grind)
    | exact superpose eq1897 eq80015
    | exact resolve eq80015 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80015
  have eq80025 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq80024
  have eq80084 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq80025 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq80025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80025
  have eq80092 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq80084
    | exact resolve eq80084 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80084
  have eq80103 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq80092
       have r₂ := eq28
       grind)
    | exact resolve eq80092 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80092
  have eq80258 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq80103 eq7894
    | exact resolve eq7894 eq80103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7894 eq80103
  have eq80264 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq80258
       have i₂ := eq1897 sF2 sF2
       grind)
    | exact superpose eq1897 eq80258
    | exact resolve eq80258 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897 eq80258
  have eq80265 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq80264
  have eq80299 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq80265 eq30
    | exact resolve eq30 eq80265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq80265
  have eq80525 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq80299
    | exact resolve eq80299 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq80299
  have eq80526 : x = y := by grind
  clear eq80525
  have eq80545 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq80526
       grind)
    | exact superpose eq80526 eq19
    | exact resolve eq19 eq80526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq80546 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq80526
       grind)
    | exact superpose eq80526 eq25
    | exact resolve eq25 eq80526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq80526
  have eq80769 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq80546
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq80546
    | exact resolve eq80546 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq80546
  have eq80788 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq80769 eq27
    | exact resolve eq27 eq80769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq80769
  have eq81277 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq80788 eq71
    | exact resolve eq71 eq80788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq80788
  have eq81466 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq81277
       have i₂ := eq80545
       grind)
    | exact superpose eq80545 eq81277
    | exact resolve eq81277 eq80545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80545 eq81277
  have eq81476 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq81466 eq15
    | exact resolve eq15 eq81466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81466
  have eq81557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq81476
    | exact resolve eq81476 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq81476
  have eq81578 : False := by grind
  exact eq81578

/-- `Equation2286`: `x = (x ◇ (y ◇ (z ◇ w))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_y_pxy_pyx_Equation2286 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2286 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2286.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X1) = X0 := by
    intro X0 X1 X2 X3
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k x y) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
  have eq59 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 X3) (M.op X4 X5)))) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X1 (M.op X0 (M.op (M.op X2 X3) (M.op X4 X5))) X2 X3
       have i₂ := eq14 X0 (M.op X2 X3) X4 X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq87 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq16
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq129 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  clear eq37
  have eq399 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X2 X1 X0 x x (M.op (M.op x x) (M.op x x))
       have i₂ := eq59 x X0 x x x x
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq476 : ∀ X0 : G, x = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq399 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq399
    | (have j0 := eq399 X0 x y
       grind)
    | exact resolve eq399 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq399
    | (have j0 := eq399 X0 (σ x) (σ y)
       grind)
    | exact resolve eq399 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq399 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq399
    | (have j0 := eq399 y X0 x
       grind)
    | exact resolve eq399 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq652 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq68 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq6536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq6537 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq6536
    | exact resolve eq6536 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6536
  have eq6548 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq6537
       have r₂ := eq27
       grind)
    | exact resolve eq6537 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6537
  have eq6550 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq6548
    | exact resolve eq6548 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6548
  have eq6689 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6550 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq6550
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq6550
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq6550
       grind)
    | exact resolve eq13 eq6550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6550
  have eq6707 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq6689
  have eq6770 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6707 eq97
    | exact resolve eq97 eq6707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq6707
  have eq6789 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq6770
    | exact resolve eq6770 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq6770
  have eq6792 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq6789
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq6789
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq6789
       have r₂ := eq13 y x
       grind)
    | exact resolve eq6789 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6789
  have eq6794 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq6792
       grind)
    | exact superpose eq6792 eq87
    | exact resolve eq87 eq6792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq6801 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq6792
       grind)
    | exact superpose eq6792 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq6792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6792
  have eq6802 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6801
  have eq6804 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6802
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6802
    | exact resolve eq6802 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6802
  have eq6805 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6804
  have eq6812 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6794
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6794
    | exact resolve eq6794 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6794
  have eq6948 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq6805
       grind)
    | exact superpose eq6805 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq6805
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq6805
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq6805
       grind)
    | exact resolve eq12 eq6805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6805
  have eq6968 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6948
  have eq6972 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6968
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6968
    | exact resolve eq6968 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6968
  have eq6973 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6972
  have eq6974 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6973
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6973
    | exact resolve eq6973 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6973
  have eq6987 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6812 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq6812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6812
  have eq6988 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6987
  have eq6992 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq6988
    | exact resolve eq6988 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6988
  have eq6993 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6992
  have eq7205 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq6974
       grind)
    | exact superpose eq6974 eq44
    | exact resolve eq44 eq6974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6974
  have eq7219 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq7205
    | exact resolve eq7205 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7205
  have eq7224 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6993 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq6993
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq6993
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq6993
       grind)
    | exact resolve eq12 eq6993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6993
  have eq7244 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7224
  have eq7248 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7244
    | exact resolve eq7244 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7244
  have eq7249 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7248
  have eq7250 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7249
    | exact resolve eq7249 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7249
  have eq7620 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7250 eq7219
    | exact resolve eq7219 eq7250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7219 eq7250
  have eq7622 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7620
  have eq7624 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7622
       have r₂ := eq27
       grind)
    | exact resolve eq7622 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7622
  have eq7627 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7624 eq51
    | (have r₁ := eq51
       have r₂ := eq7624
       grind)
    | exact resolve eq51 eq7624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq7624
  have eq7642 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7627
  have eq7649 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7642 eq55
    | exact resolve eq55 eq7642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq7642
  have eq7672 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq7649
    | exact resolve eq7649 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq7649
  have eq7676 : y = (k x y) := by
    first
    | (have r₁ := eq7672
       have r₂ := eq50
       grind)
    | exact resolve eq7672 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq7672
  have eq7809 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq7676
       grind)
    | exact superpose eq7676 eq44
    | exact resolve eq44 eq7676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7817 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq7676
       grind)
    | exact superpose eq7676 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq7676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7818 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq7817
  have eq7820 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7818
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7818
    | exact resolve eq7818 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7818
  have eq7827 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq7809
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7809
    | exact resolve eq7809 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7809
  have eq7859 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq476 x
       have i₂ := eq7820
       grind)
    | exact superpose eq7820 eq476
    | exact resolve eq476 eq7820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq7861 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq487 y
       have i₂ := eq7820
       grind)
    | exact superpose eq7820 eq487
    | exact resolve eq487 eq7820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq7862 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq7820
       grind)
    | exact superpose eq7820 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq7820
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq7820
       grind)
    | exact resolve eq12 eq7820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7820
  have eq7882 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq7862
  have eq7886 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7882
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7882
    | exact resolve eq7882 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7882
  have eq7887 : x = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq7886
  have eq7888 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7887
       have i₂ := eq7676
       grind)
    | exact superpose eq7676 eq7887
    | exact resolve eq7887 eq7676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7676 eq7887
  have eq7889 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7888
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7888
    | exact resolve eq7888 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7888
  have eq7956 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq8220 : x = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq7889 eq7859
    | exact resolve eq7859 eq7889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7859
  have eq8240 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8220
       have r₂ := eq7956
       grind)
    | exact resolve eq8220 eq7956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8220
  have eq8241 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq7889 eq7861
    | exact resolve eq7861 eq7889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7861 eq7889
  have eq8274 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8241
       have r₂ := eq7956
       grind)
    | exact resolve eq8241 eq7956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8241
  have eq9217 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8240
       have i₂ := eq8274
       grind)
    | exact superpose eq8274 eq8240
    | exact resolve eq8240 eq8274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8240 eq8274
  have eq9239 : x = y ∨ x = (M.op x y) := by grind
  clear eq9217
  have eq9242 : x = (M.op x y) := by
    first
    | (have r₁ := eq9239
       have r₂ := eq7956
       grind)
    | exact resolve eq9239 eq7956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7956 eq9239
  have eq9245 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq9242 eq20
    | exact resolve eq20 eq9242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9262 : (σ (k x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq9242 eq129
    | exact resolve eq129 eq9242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9242
  have eq9347 : (k (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq9262
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq9262
    | exact resolve eq9262 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq9262
  have eq9361 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq9245
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9245
    | exact resolve eq9245 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9245
  have eq9369 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq7827 eq9347
    | exact resolve eq9347 eq7827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7827 eq9347
  have eq9729 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq9361 eq26
    | exact resolve eq26 eq9361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq10036 : (σ y) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq129 eq652
    | (have j0 := eq652 y (M.op x y)
       grind)
    | exact resolve eq652 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq652
  have eq10057 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq9369 eq10036
    | (have r₁ := eq10036
       have r₂ := eq9369
       grind)
    | exact resolve eq10036 eq9369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10036
  have eq10160 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq10057
       have r₂ := eq24
       grind)
    | exact resolve eq10057 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10057
  have eq10260 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq10160
    | exact resolve eq10160 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10160
  have eq10353 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq10260
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10260
    | exact resolve eq10260 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10260
  have eq10440 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq10353
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10353
    | exact resolve eq10353 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10353
  have eq10523 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10440
    | exact resolve eq10440 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10440
  have eq10581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq9729 eq10523
    | exact resolve eq10523 eq9729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10523
  have eq10631 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq10581
       have r₂ := eq27
       grind)
    | exact resolve eq10581 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10581
  have eq10759 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq10631 eq477
    | exact resolve eq477 eq10631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10760 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq10631 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ y)
       have r₂ := eq10631
       grind)
    | exact resolve eq12 eq10631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10780 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq10760
  have eq10782 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq9729 eq10780
    | exact resolve eq10780 eq9729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10780
  have eq10783 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq9361 eq10759
    | exact resolve eq10759 eq9361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10759
  have eq10785 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq10782
       have r₂ := eq27
       grind)
    | exact resolve eq10782 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10782
  have eq10786 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq9729 eq10785
    | exact resolve eq10785 eq9729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9729 eq10785
  have eq10787 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9369 eq10786
    | exact resolve eq10786 eq9369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9369 eq10786
  have eq10789 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq10787 eq27
    | exact resolve eq27 eq10787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq10864 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq10787 eq10783
    | exact resolve eq10783 eq10787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10783
  have eq10868 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq10864 eq477
    | exact resolve eq477 eq10864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq10864
  have eq10888 : (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq10787 eq10868
    | exact resolve eq10868 eq10787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10787 eq10868
  have eq10890 : (σ x) = (σ y) := by
    first
    | exact superpose eq10631 eq10888
    | exact resolve eq10888 eq10631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10631 eq10888
  have eq10892 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9361 eq10890
    | exact resolve eq10890 eq9361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9361 eq10890
  have eq10893 : False := by grind
  exact eq10893
