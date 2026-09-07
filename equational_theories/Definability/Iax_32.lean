import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation55`: `x = x ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation55 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law55 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law55.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op X0 X0) X0
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq23 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq17 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq25 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1
       have i₂ := eq12 X1 X0
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
  have eq26 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq19
  have eq35 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq32
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq24
    | exact resolve eq24 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq24 (τ X0) X1
       grind)
    | exact superpose eq24 eq20
    | (have j1 := eq24 (τ X0) X1
       grind)
    | exact resolve eq20 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq58 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq24 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq81 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X1) X0
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq8
    | (have j1 := eq25 X1 X0
       grind)
    | exact resolve eq8 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq86 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq88 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
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
  have eq100 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq86
    | exact resolve eq86 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq200 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (σ X1)
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq17
    | (have j1 := eq26 X0 X1
       grind)
    | exact resolve eq17 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq100 X1
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq100
    | (have j1 := eq26 X0 X1
       grind)
    | exact resolve eq100 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq100
  have eq244 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq226 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq226
    | (have j0 := eq226 X0 X1
       grind)
    | exact resolve eq226 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq578 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq654 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq578 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq578
    | (have j0 := eq578 X0 X1
       grind)
    | exact resolve eq578 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq679 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq726 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq679 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq679
    | (have j0 := eq679 X0 X1
       grind)
    | exact resolve eq679 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq780 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1
       have i₂ := eq654 X0 X1
       grind)
    | (have i₁ := eq17 X0
       have i₂ := eq654 (M.op X0 X0) X1
       grind)
    | exact superpose eq654 eq17
    | (have j1 := eq654 X0 X1
       grind)
    | exact resolve eq17 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1066 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq17 (σ X0)
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq17
    | (have j1 := eq52 X0 X0
       grind)
    | exact resolve eq17 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq52
  have eq1579 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq81
  have eq1820 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq200 x y
       grind)
    | exact superpose eq200 eq14
    | (have j1 := eq200 x y
       grind)
    | exact resolve eq14 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1840 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq200 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq5615 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1840 (τ X1) (τ X0)
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq1840
    | (have j0 := eq1840 (τ X1) (τ X0)
       grind)
    | exact resolve eq1840 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq5643 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5615 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5615
    | (have j0 := eq5615 X0 X1
       grind)
    | exact resolve eq5615 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5615
  have eq5651 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5643 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5643
    | (have j0 := eq5643 X0 X1
       grind)
    | exact resolve eq5643 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5643
  have eq5654 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5651 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5651
    | (have j0 := eq5651 X0 X1
       grind)
    | exact resolve eq5651 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5651
  have eq5655 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5654 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5654
    | (have j0 := eq5654 X0 X1
       grind)
    | exact resolve eq5654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5654
  have eq9697 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
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
  clear eq244
  have eq9733 : y = (k y x) := by
    first
    | (have j1 := eq726 x y
       grind)
    | (have r₁ := eq9697
       have r₂ := eq726 x y
       grind)
    | exact resolve eq9697 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq9697
  have eq9897 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23 x y
       have i₂ := eq9733
       grind)
    | exact superpose eq9733 eq23
    | (have j0 := eq23 x y
       grind)
    | exact resolve eq23 eq9733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq9900 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq780 x y
       have i₂ := eq9733
       grind)
    | exact superpose eq9733 eq780
    | (have j0 := eq780 x y
       grind)
    | exact resolve eq780 eq9733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9901 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1840 x y
       have i₂ := eq9733
       grind)
    | exact superpose eq9733 eq1840
    | (have j0 := eq1840 x y
       grind)
    | exact resolve eq1840 eq9733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9903 : x ≠ y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5655 y x
       have i₂ := eq9733
       grind)
    | exact superpose eq9733 eq5655
    | (have j0 := eq5655 y x
       grind)
    | exact resolve eq5655 eq9733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9733
  have eq11343 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 y x
       have i₂ := eq9897
       grind)
    | exact superpose eq9897 eq8
    | exact resolve eq8 eq9897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14135 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11343
       have i₂ := eq9897
       grind)
    | exact superpose eq9897 eq11343
    | exact resolve eq11343 eq9897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9897 eq11343
  have eq14151 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14135
       have r₂ := eq9903
       grind)
    | exact resolve eq14135 eq9903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9903 eq14135
  have eq14726 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq58 y y
       have i₂ := eq14151
       grind)
    | exact superpose eq14151 eq58
    | (have j0 := eq58 y y
       grind)
    | (have r₁ := eq58 y y
       have r₂ := eq14151
       grind)
    | exact resolve eq58 eq14151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq14151
  have eq14735 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq14726
  have eq14970 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1840 y y
       have i₂ := eq14735
       grind)
    | exact superpose eq14735 eq1840
    | (have j0 := eq1840 y y
       grind)
    | exact resolve eq1840 eq14735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14735
  have eq14974 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14970
  have eq18200 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1820
       have i₂ := eq654 x y
       grind)
    | exact superpose eq654 eq1820
    | (have j1 := eq654 x y
       grind)
    | (have r₁ := eq1820
       have r₂ := eq654 x y
       grind)
    | exact resolve eq1820 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq18202 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1820
       have i₂ := eq780 x y
       grind)
    | exact superpose eq780 eq1820
    | (have j1 := eq780 (σ x) (σ y)
       grind)
    | (have r₁ := eq1820
       have r₂ := eq780 x y
       grind)
    | exact resolve eq1820 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780 eq1820
  have eq18207 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18202
  have eq18209 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq18200
  have eq18390 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq18209
       grind)
    | exact superpose eq18209 eq14
    | exact resolve eq14 eq18209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18209
  have eq18985 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq18207
       grind)
    | exact superpose eq18207 eq14
    | exact resolve eq14 eq18207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18996 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88 (σ x) y
       have i₂ := eq18207
       grind)
    | exact superpose eq18207 eq88
    | (have j0 := eq88 (σ x) y
       grind)
    | exact resolve eq88 eq18207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq18207
  have eq19019 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18996
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq18996
    | exact resolve eq18996 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18996
  have eq19036 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq5655 y x
       grind)
    | (have r₁ := eq19019
       have r₂ := eq5655 y x
       grind)
    | exact resolve eq19019 eq5655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19019
  have eq19167 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18985
       have i₂ := eq9900
       grind)
    | exact superpose eq9900 eq18985
    | exact resolve eq18985 eq9900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9900 eq18985
  have eq19170 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq19167
  have eq19739 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14974
       have i₂ := eq19036
       grind)
    | exact superpose eq19036 eq14974
    | exact resolve eq14974 eq19036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14974 eq19036
  have eq19811 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq19739
  have eq19838 : x = (M.op x y) := by
    first
    | (have r₁ := eq19811
       have r₂ := eq19170
       grind)
    | exact resolve eq19811 eq19170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19170 eq19811
  have eq20287 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18390
       have i₂ := eq19838
       grind)
    | exact superpose eq19838 eq18390
    | exact resolve eq18390 eq19838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18390
  have eq20288 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq8 y x
       have i₂ := eq19838
       grind)
    | exact superpose eq19838 eq8
    | exact resolve eq8 eq19838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20303 : x = (M.op y y) := by grind
  clear eq20287
  have eq20433 : x = (k y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1579 y
       have i₂ := eq20303
       grind)
    | exact superpose eq20303 eq1579
    | exact resolve eq1579 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1579
  have eq20438 : y = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq8 y y
       have i₂ := eq20303
       grind)
    | exact superpose eq20303 eq8
    | exact resolve eq8 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21689 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1066 y
       have i₂ := eq20433
       grind)
    | exact superpose eq20433 eq1066
    | exact resolve eq1066 eq20433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066 eq20433
  have eq21723 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq21689
       have r₂ := eq9901
       grind)
    | exact resolve eq21689 eq9901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9901 eq21689
  have eq29800 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21723
       grind)
    | exact superpose eq21723 eq14
    | exact resolve eq14 eq21723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21723
  have eq29848 : (σ x) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq29800
       have i₂ := eq19838
       grind)
    | exact superpose eq19838 eq29800
    | exact resolve eq29800 eq19838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19838 eq29800
  have eq29849 : x = (k x x) := by grind
  clear eq29848
  have eq30503 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1840 x x
       have i₂ := eq29849
       grind)
    | exact superpose eq29849 eq1840
    | (have j0 := eq1840 x x
       grind)
    | exact resolve eq1840 eq29849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840
  have eq30505 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5655 x x
       have i₂ := eq29849
       grind)
    | exact superpose eq29849 eq5655
    | (have j0 := eq5655 x x
       grind)
    | (have r₁ := eq5655 x x
       have r₂ := eq29849
       grind)
    | exact resolve eq5655 eq29849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5655 eq29849
  have eq30506 : x = (M.op x x) := by grind
  clear eq30505
  have eq30507 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq30503
  have eq31247 : y = (M.op y x) := by
    first
    | (have i₁ := eq20288
       have i₂ := eq30506
       grind)
    | exact superpose eq30506 eq20288
    | exact resolve eq20288 eq30506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20288
  have eq31988 : y = (M.op y y) := by
    first
    | (have i₁ := eq20438
       have i₂ := eq31247
       grind)
    | exact superpose eq31247 eq20438
    | exact resolve eq20438 eq31247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20438 eq31247
  have eq32020 : x = y := by
    first
    | (have i₁ := eq31988
       have i₂ := eq20303
       grind)
    | exact superpose eq20303 eq31988
    | exact resolve eq31988 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20303 eq31988
  have eq32167 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq32020
       grind)
    | exact superpose eq32020 eq14
    | exact resolve eq14 eq32020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32020
  have eq32236 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq32167
       have i₂ := eq30506
       grind)
    | exact superpose eq30506 eq32167
    | exact resolve eq32167 eq30506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30506 eq32167
  have eq32237 : False := by grind
  exact eq32237

/-- `Equation55`: `x = x ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation55 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law55 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law55.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq17 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op X0 X0) X0
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq23 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq17 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq25 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 (M.op X1 X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31
    | exact resolve eq31 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq48 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq31
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq53 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq46
    | exact resolve eq46 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq24
    | exact resolve eq24 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq24 (τ X0) X1
       grind)
    | exact superpose eq24 eq19
    | (have j1 := eq24 (τ X0) X1
       grind)
    | exact resolve eq19 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq24 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq82 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X1) X0
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq8
    | (have j1 := eq25 X1 X0
       grind)
    | exact resolve eq8 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq202 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (σ X1)
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq17
    | (have j1 := eq26 X0 X1
       grind)
    | exact resolve eq17 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq53
    | (have j1 := eq26 X0 X1
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq53
  have eq247 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq228 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq228
    | (have j0 := eq228 X0 X1
       grind)
    | exact resolve eq228 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq583 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq28
    | exact resolve eq28 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq659 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq583 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq583
    | (have j0 := eq583 X0 X1
       grind)
    | exact resolve eq583 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq684 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq59
    | exact resolve eq59 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq731 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq684 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq684
    | (have j0 := eq684 X0 X1
       grind)
    | exact resolve eq684 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq785 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1
       have i₂ := eq659 X0 X1
       grind)
    | (have i₁ := eq17 X0
       have i₂ := eq659 (M.op X0 X0) X1
       grind)
    | exact superpose eq659 eq17
    | (have j1 := eq659 X0 X1
       grind)
    | exact resolve eq17 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1071 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq17 (σ x)
       have i₂ := eq54 x x
       grind)
    | exact superpose eq54 eq17
    | (have j1 := eq54 X0 X0
       grind)
    | exact resolve eq17 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq54
  have eq1591 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq82
  have eq1835 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq202 x y
       grind)
    | exact superpose eq202 eq14
    | (have j1 := eq202 x y
       grind)
    | exact resolve eq14 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1855 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq4862 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1855 (τ X0) (τ X1)
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq1855
    | (have j0 := eq1855 (τ X0) (τ X1)
       grind)
    | exact resolve eq1855 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq4897 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4862 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4862
    | (have j0 := eq4862 X0 X1
       grind)
    | exact resolve eq4862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4862
  have eq4902 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4897 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4897
    | (have j0 := eq4897 X0 X1
       grind)
    | exact resolve eq4897 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4897
  have eq4903 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4902 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4902
    | (have j0 := eq4902 X0 X1
       grind)
    | exact resolve eq4902 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4902
  have eq4904 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4903 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4903
    | (have j0 := eq4903 X0 X1
       grind)
    | exact resolve eq4903 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4903
  have eq8306 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq247 x y
       grind)
    | exact superpose eq247 eq14
    | (have j1 := eq247 x y
       grind)
    | exact resolve eq14 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq8340 : y = (k x y) := by
    first
    | (have j1 := eq731 x y
       grind)
    | (have r₁ := eq8306
       have r₂ := eq731 x y
       grind)
    | exact resolve eq8306 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq8306
  have eq8940 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23 x y
       have i₂ := eq8340
       grind)
    | exact superpose eq8340 eq23
    | (have j0 := eq23 x y
       grind)
    | exact resolve eq23 eq8340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq8943 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq785 x y
       have i₂ := eq8340
       grind)
    | exact superpose eq8340 eq785
    | (have j0 := eq785 x y
       grind)
    | exact resolve eq785 eq8340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8944 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1855 x y
       have i₂ := eq8340
       grind)
    | exact superpose eq8340 eq1855
    | (have j0 := eq1855 x y
       grind)
    | exact resolve eq1855 eq8340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8946 : x ≠ y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4904 x y
       have i₂ := eq8340
       grind)
    | exact superpose eq8340 eq4904
    | (have j0 := eq4904 x y
       grind)
    | exact resolve eq4904 eq8340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8340
  have eq9835 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 y x
       have i₂ := eq8940
       grind)
    | exact superpose eq8940 eq8
    | exact resolve eq8 eq8940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12907 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9835
       have i₂ := eq8940
       grind)
    | exact superpose eq8940 eq9835
    | exact resolve eq9835 eq8940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8940 eq9835
  have eq12921 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12907
       have r₂ := eq8946
       grind)
    | exact resolve eq12907 eq8946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8946 eq12907
  have eq13154 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60 y y
       have i₂ := eq12921
       grind)
    | exact superpose eq12921 eq60
    | (have j0 := eq60 y y
       grind)
    | (have r₁ := eq60 y y
       have r₂ := eq12921
       grind)
    | exact resolve eq60 eq12921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq12921
  have eq13163 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq13154
  have eq13995 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1855 y y
       have i₂ := eq13163
       grind)
    | exact superpose eq13163 eq1855
    | (have j0 := eq1855 y y
       grind)
    | exact resolve eq1855 eq13163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13163
  have eq13999 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13995
  have eq18057 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1835
       have i₂ := eq659 x y
       grind)
    | exact superpose eq659 eq1835
    | (have j1 := eq659 x y
       grind)
    | (have r₁ := eq1835
       have r₂ := eq659 x y
       grind)
    | exact resolve eq1835 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq18059 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1835
       have i₂ := eq785 x y
       grind)
    | exact superpose eq785 eq1835
    | (have j1 := eq785 (σ x) (σ y)
       grind)
    | (have r₁ := eq1835
       have r₂ := eq785 x y
       grind)
    | exact resolve eq1835 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785 eq1835
  have eq18064 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18059
  have eq18066 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq18057
  have eq18085 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq18066
       grind)
    | exact superpose eq18066 eq14
    | exact resolve eq14 eq18066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18066
  have eq18729 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq18064
       grind)
    | exact superpose eq18064 eq14
    | exact resolve eq14 eq18064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18741 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48 (σ x) y
       have i₂ := eq18064
       grind)
    | exact superpose eq18064 eq48
    | (have j0 := eq48 (σ x) y
       grind)
    | exact resolve eq48 eq18064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq18064
  have eq18762 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18741
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq18741
    | exact resolve eq18741 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18741
  have eq18779 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq4904 x y
       grind)
    | (have r₁ := eq18762
       have r₂ := eq4904 x y
       grind)
    | exact resolve eq18762 eq4904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18762
  have eq18865 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18729
       have i₂ := eq8943
       grind)
    | exact superpose eq8943 eq18729
    | exact resolve eq18729 eq8943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8943 eq18729
  have eq18868 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq18865
  have eq19150 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13999
       have i₂ := eq18779
       grind)
    | exact superpose eq18779 eq13999
    | exact resolve eq13999 eq18779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13999 eq18779
  have eq19220 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq19150
  have eq19245 : x = (M.op x y) := by
    first
    | (have r₁ := eq19220
       have r₂ := eq18868
       grind)
    | exact resolve eq19220 eq18868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18868 eq19220
  have eq19676 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18085
       have i₂ := eq19245
       grind)
    | exact superpose eq19245 eq18085
    | exact resolve eq18085 eq19245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18085
  have eq19677 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq8 y x
       have i₂ := eq19245
       grind)
    | exact superpose eq19245 eq8
    | exact resolve eq8 eq19245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19692 : x = (M.op y y) := by grind
  clear eq19676
  have eq20139 : x = (k y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1591 y
       have i₂ := eq19692
       grind)
    | exact superpose eq19692 eq1591
    | exact resolve eq1591 eq19692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1591
  have eq20143 : y = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq8 y y
       have i₂ := eq19692
       grind)
    | exact superpose eq19692 eq8
    | exact resolve eq8 eq19692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21358 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1071 y
       have i₂ := eq20139
       grind)
    | exact superpose eq20139 eq1071
    | exact resolve eq1071 eq20139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071 eq20139
  have eq21502 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq21358
       have r₂ := eq8944
       grind)
    | exact resolve eq21358 eq8944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8944 eq21358
  have eq28377 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21502
       grind)
    | exact superpose eq21502 eq14
    | exact resolve eq14 eq21502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21502
  have eq28425 : (σ x) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq28377
       have i₂ := eq19245
       grind)
    | exact superpose eq19245 eq28377
    | exact resolve eq28377 eq19245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19245 eq28377
  have eq28426 : x = (k x x) := by grind
  clear eq28425
  have eq29091 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1855 x x
       have i₂ := eq28426
       grind)
    | exact superpose eq28426 eq1855
    | (have j0 := eq1855 x x
       grind)
    | exact resolve eq1855 eq28426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1855
  have eq29093 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4904 x x
       have i₂ := eq28426
       grind)
    | exact superpose eq28426 eq4904
    | (have j0 := eq4904 x x
       grind)
    | (have r₁ := eq4904 x x
       have r₂ := eq28426
       grind)
    | exact resolve eq4904 eq28426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4904 eq28426
  have eq29094 : x = (M.op x x) := by grind
  clear eq29093
  have eq29095 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq29091
  have eq29810 : y = (M.op y x) := by
    first
    | (have i₁ := eq19677
       have i₂ := eq29094
       grind)
    | exact superpose eq29094 eq19677
    | exact resolve eq19677 eq29094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19677
  have eq30611 : y = (M.op y y) := by
    first
    | (have i₁ := eq20143
       have i₂ := eq29810
       grind)
    | exact superpose eq29810 eq20143
    | exact resolve eq20143 eq29810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20143 eq29810
  have eq30643 : x = y := by
    first
    | (have i₁ := eq30611
       have i₂ := eq19692
       grind)
    | exact superpose eq19692 eq30611
    | exact resolve eq30611 eq19692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19692 eq30611
  have eq31291 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30643
       grind)
    | exact superpose eq30643 eq14
    | exact resolve eq14 eq30643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30643
  have eq31358 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq31291
       have i₂ := eq29094
       grind)
    | exact superpose eq29094 eq31291
    | exact resolve eq31291 eq29094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29094 eq31291
  have eq31359 : False := by grind
  exact eq31359

/-- `Equation56`: `x = x ◇ (y ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation56 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law56 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law56.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq8 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X1 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq11 X0 (M.op X1 (M.op X1 X1))
       have r₂ := eq8 (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq19 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq26 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq27 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq26 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
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
  have eq47 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X1 X1))) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X0
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq12
    | (have j0 := eq12 X2 X0
       grind)
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq71 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X0
       have i₂ := eq27 X0 X0 X2
       grind)
    | exact superpose eq27 eq8
    | (have j1 := eq27 X0 X1 X2
       grind)
    | exact resolve eq8 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq30 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq206 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq71 X1 X2 (τ X0)
       grind)
    | exact superpose eq71 eq17
    | (have j1 := eq71 X1 X2 X2
       grind)
    | exact resolve eq17 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq71
  have eq259 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X1 X1))) ≠ (k X0 (M.op X1 (M.op X1 X1))) ∨ (k X0 (M.op X1 (M.op X1 X1))) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq134 X1 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq134
    | exact resolve eq134 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq264 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq134 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq267 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X1 X1))) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq259 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq315 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq264 (σ X0)
       grind)
    | exact superpose eq264 eq13
    | exact resolve eq13 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq54 X0 X0
       have i₂ := eq264 (τ X0)
       grind)
    | exact superpose eq264 eq54
    | exact resolve eq54 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq317 X0
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq317
    | exact resolve eq317 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq327 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq315 X0
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq315
    | exact resolve eq315 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq380 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (τ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (τ X0)
       have i₂ := eq325 X0
       grind)
    | exact superpose eq325 eq8
    | exact resolve eq8 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ X0)
       have i₂ := eq327 X0
       grind)
    | exact superpose eq327 eq8
    | exact resolve eq8 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq29
    | (have j0 := eq29 X0 X1
       grind)
    | exact resolve eq29 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq526 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq466
    | (have j0 := eq466 X0 X1
       grind)
    | exact resolve eq466 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq582 : ∀ X0 X1 : G, (τ (k (σ X0) (M.op X1 (M.op X1 X1)))) = (k X0 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X0)
       have i₂ := eq267 (σ X0) X1
       grind)
    | (have i₁ := eq37 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq267 (σ X0) X1
       grind)
    | exact superpose eq267 eq37
    | exact resolve eq37 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq587 : ∀ X0 X1 : G, (k X0 X0) = (τ (k (σ X0) (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq582 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq582
    | exact resolve eq582 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq612 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (τ (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq587 X0 X1
       have i₂ := eq37 X0 (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq37 eq587
    | exact resolve eq587 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq684 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op X0 (M.op X0 X0))) (τ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq380 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq8 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq8 eq380
    | exact resolve eq380 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq728 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq684 X0 X1
       have i₂ := eq325 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq325 eq684
    | exact resolve eq684 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq737 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq728 X0 X1
       have i₂ := eq8 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq8 eq728
    | exact resolve eq728 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq812 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (σ X0) (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq737 (σ X0) X1
       have i₂ := eq327 X0
       grind)
    | exact superpose eq327 eq737
    | exact resolve eq737 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq969 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq448 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq8 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq8 eq448
    | exact resolve eq448 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq1019 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq969 X0 X1
       have i₂ := eq327 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq327 eq969
    | exact resolve eq969 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq1033 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1019 X0 X1
       have i₂ := eq8 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq8 eq1019
    | exact resolve eq1019 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1183 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1033 X0 X1
       have i₂ := eq27 X0 X0 X2
       grind)
    | exact superpose eq27 eq1033
    | (have j1 := eq27 X0 X1 X2
       grind)
    | exact resolve eq1033 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1033
  have eq2166 : ∀ X0 X1 : G, (τ (k X0 X0)) = (k (τ X0) (τ (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X0
       have i₂ := eq612 (τ X0) X1
       grind)
    | (have i₁ := eq54 (M.op X1 (M.op X1 X1)) X1
       have i₂ := eq612 (τ X1) X1
       grind)
    | exact superpose eq612 eq54
    | exact resolve eq54 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq2189 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (k X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2166 X0 X1
       have i₂ := eq54 (M.op X1 (M.op X1 X1)) X0
       grind)
    | exact superpose eq54 eq2166
    | exact resolve eq2166 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq2166
  have eq2230 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2189 X0 X1
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq2189
    | exact resolve eq2189 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq2189
  have eq8459 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq128 x y X0
       grind)
    | exact superpose eq128 eq14
    | (have j1 := eq128 X0 y X0
       grind)
    | exact resolve eq14 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq10511 : ∀ X0 X2 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq2230 X0 x
       have i₂ := eq47 X0 x X2
       grind)
    | exact superpose eq47 eq2230
    | (have j1 := eq47 X0 x X2
       grind)
    | exact resolve eq2230 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq2230
  have eq13122 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq1183 y (σ x) X0
       grind)
    | exact superpose eq1183 eq14
    | (have j1 := eq1183 y x X0
       grind)
    | exact resolve eq14 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq44865 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206 (σ X0) X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq206
    | (have j0 := eq206 X0 X1 X2
       grind)
    | exact resolve eq206 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq45464 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44865 X0 X1 X2
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq44865
    | (have j0 := eq44865 X0 X1 X2
       grind)
    | exact resolve eq44865 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44865
  have eq91762 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq8459 X0
       have i₂ := eq526 x y
       grind)
    | exact superpose eq526 eq8459
    | (have j0 := eq8459 X0
       have j1 := eq526 X0 y
       grind)
    | (have r₁ := eq8459 X0
       have r₂ := eq526 x y
       grind)
    | exact resolve eq8459 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq8459
  have eq91763 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq91762 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91762
  have eq92281 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq10511 (σ y) X0
       have i₂ := eq91763 X0
       grind)
    | exact superpose eq91763 eq10511
    | (have j0 := eq10511 (σ y) x
       grind)
    | exact resolve eq10511 eq91763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10511
  have eq92289 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ y))) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq37 X0 (σ y)
       have i₂ := eq91763 (σ X0)
       grind)
    | exact superpose eq91763 eq37
    | exact resolve eq37 eq91763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq91763
  have eq92308 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq92289 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq92289
    | exact resolve eq92289 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92289
  have eq92313 : ∀ X0 : G, (τ (σ y)) = (τ (σ (M.op y y))) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq92281 X0
       have i₂ := eq327 y
       grind)
    | exact superpose eq327 eq92281
    | (have j0 := eq92281 X0
       grind)
    | exact resolve eq92281 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92281
  have eq92553 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (k X0 y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq92308 X0
       have i₂ := eq327 X0
       grind)
    | exact superpose eq327 eq92308
    | exact resolve eq92308 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92308
  have eq92557 : ∀ X0 : G, (τ (σ y)) = (M.op y y) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq92313 X0
       have i₂ := eq9 (M.op y y)
       grind)
    | exact superpose eq9 eq92313
    | (have j0 := eq92313 X0
       grind)
    | exact resolve eq92313 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92313
  have eq92650 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq92553 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq92553
    | exact resolve eq92553 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92553
  have eq92653 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq92557 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq92557
    | (have j0 := eq92557 X0
       grind)
    | exact resolve eq92557 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92557
  have eq92654 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq92653 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92653
  have eq92674 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq92650 X0
       have j1 := eq11 X0 y
       grind)
    | (have r₁ := eq92650 X0
       have r₂ := eq11 X0 y
       grind)
    | exact resolve eq92650 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92650
  have eq94632 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (σ X0) (σ (k X0 y))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq812 X0 X1
       have i₂ := eq92674 X0
       grind)
    | exact superpose eq92674 eq812
    | exact resolve eq812 eq92674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq94813 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq327 X0
       have i₂ := eq92674 (σ X0)
       grind)
    | exact superpose eq92674 eq327
    | exact resolve eq327 eq92674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq94833 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) y) := by
    intro X0
    first
    | (have i₁ := eq325 X0
       have i₂ := eq92674 (τ X0)
       grind)
    | exact superpose eq92674 eq325
    | exact resolve eq325 eq92674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq94895 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 y)) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45464 X0 y X1
       have i₂ := eq92674 X0
       grind)
    | exact superpose eq92674 eq45464
    | (have j0 := eq45464 X0 y X1
       grind)
    | exact resolve eq45464 eq92674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45464
  have eq369279 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq92654 (σ x)
       grind)
    | exact superpose eq92654 eq14
    | exact resolve eq14 eq92654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92654
  have eq369330 : (σ (M.op x y)) ≠ (k (σ x) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq369279
       have i₂ := eq92674 (σ x)
       grind)
    | exact superpose eq92674 eq369279
    | exact resolve eq369279 eq92674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92674 eq369279
  have eq369602 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq369330
       have i₂ := eq94813 x
       grind)
    | exact superpose eq94813 eq369330
    | exact resolve eq369330 eq94813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94813 eq369330
  have eq369679 : y = (M.op y y) := by
    first
    | (have j1 := eq94895 x y
       grind)
    | (have r₁ := eq369602
       have r₂ := eq94895 x x
       grind)
    | exact resolve eq369602 eq94895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94895 eq369602
  have eq372846 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 y
       have i₂ := eq369679
       grind)
    | exact superpose eq369679 eq8
    | exact resolve eq8 eq369679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373162 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq372846 X0
       have i₂ := eq369679
       grind)
    | exact superpose eq369679 eq372846
    | exact resolve eq372846 eq369679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369679 eq372846
  have eq374631 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13122 X0
       have i₂ := eq373162 x
       grind)
    | exact superpose eq373162 eq13122
    | (have j0 := eq13122 X0
       grind)
    | exact resolve eq13122 eq373162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13122
  have eq374634 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq374631 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374631
  have eq374645 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq374634 X0
       have i₂ := eq373162 X0
       grind)
    | exact superpose eq373162 eq374634
    | exact resolve eq374634 eq373162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374634
  have eq376287 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (σ X0) (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq94632 X0 X1
       have i₂ := eq374645 X0
       grind)
    | exact superpose eq374645 eq94632
    | exact resolve eq94632 eq374645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94632
  have eq376540 : ∀ X0 X1 : G, (M.op X1 (k (τ (σ X0)) y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq376287 X0 X1
       have i₂ := eq94833 (σ X0)
       grind)
    | exact superpose eq94833 eq376287
    | exact resolve eq376287 eq94833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94833 eq376287
  have eq376599 : ∀ X0 X1 : G, (M.op X1 (τ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq376540 X0 X1
       have i₂ := eq374645 (τ (σ X0))
       grind)
    | exact superpose eq374645 eq376540
    | exact resolve eq376540 eq374645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374645 eq376540
  have eq376629 : ∀ X0 X1 : G, (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq376599 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq376599
    | exact resolve eq376599 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376599
  have eq381445 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq376629 (σ y) (σ x)
       grind)
    | exact superpose eq376629 eq14
    | exact resolve eq14 eq376629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376629
  have eq381582 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq381445
       have i₂ := eq373162 x
       grind)
    | exact superpose eq373162 eq381445
    | exact resolve eq381445 eq373162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373162 eq381445
  have eq381583 : False := by grind
  exact eq381583

/-- `Equation58`: `x = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation58 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law58 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law58.models_iff G M).mp hM
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
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq83 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq83 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq83 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq83 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq87 (σ X0) (σ X1)
       grind)
    | exact superpose eq87 eq13
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0 X1
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq103
    | exact resolve eq103 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq103
  have eq1869 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq108 x y
       grind)
    | exact superpose eq108 eq14
    | (have r₁ := eq14
       have r₂ := eq108 x y
       grind)
    | exact resolve eq14 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq1892 : False := by grind
  exact eq1892

/-- `Equation58`: `x = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pxx_pxy_Equation58 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law58 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law58.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X0))) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 (M.op X2 X0)) X3 X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) X0 x
       have i₂ := eq8 X0 x X1
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq27 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 (M.op X1 (M.op X2 X0))
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X0 (M.op X1 (M.op X2 X0))
       grind)
    | (have r₁ := eq11 X0 (M.op X1 (M.op X2 X0))
       have r₂ := eq8 X0 X1 X2
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X1) X1
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq11
    | (have j0 := eq11 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq11 (M.op X1 X0) X0
       have r₂ := eq16 X0 X1
       grind)
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq30 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq27 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq36 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq42 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
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
  clear eq18
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (k (M.op X1 (M.op X2 X0)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30 (M.op X1 (M.op X2 X0)) X3 X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq30
    | exact resolve eq30 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (k (M.op X1 (M.op X2 X0)) (M.op X3 X0)) = (k (M.op X1 (M.op X2 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 X3
       have i₂ := eq29 X1 (M.op X2 X0)
       grind)
    | exact superpose eq29 eq52
    | exact resolve eq52 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq65 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (σ X0))))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36 X0 (M.op X1 (M.op X2 (σ X0)))
       have i₂ := eq30 (σ X0) X1 X2
       grind)
    | exact superpose eq30 eq36
    | exact resolve eq36 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) (M.op X3 X2)) = (k (M.op X3 X2) (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq30 (M.op X3 X2) X4 (M.op X0 (M.op X1 X2))
       have i₂ := eq15 X2 X0 X1 X3
       grind)
    | exact superpose eq15 eq30
    | exact resolve eq30 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op (M.op X3 X2) (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X3 X2) X4 (M.op X0 (M.op X1 X2))
       have i₂ := eq15 X2 X0 X1 X3
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 X4 : G, (k (M.op X3 X2) (M.op X4 (M.op X0 (M.op X1 X2)))) = (k (M.op X3 X2) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq85 X0 X1 X2 X3 X4
       have i₂ := eq29 X3 X2
       grind)
    | exact superpose eq29 eq85
    | exact resolve eq85 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq110 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq40 x y
       grind)
    | exact superpose eq40 eq14
    | (have j1 := eq40 x y
       grind)
    | exact resolve eq14 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (σ X1))) = (M.op (M.op X2 (M.op X3 (σ X1))) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15 (σ X1) X2 X3 (σ X0)
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq15
    | (have j1 := eq40 X0 X1
       grind)
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (σ X1) (σ X0)
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq16
    | (have j1 := eq40 (k X0 X1) X1
       grind)
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (M.op X2 (σ (k X0 X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X1) X2 (σ X0)
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq8
    | (have j1 := eq40 X0 X1
       grind)
    | exact resolve eq8 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (k (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (M.op X0 X1) X0
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq30
    | exact resolve eq30 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 : G, (M.op X1 (k (M.op X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X1) X0
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq8
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k (M.op X0 X1) X1) ∨ (k (M.op X0 X1) X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq11
    | exact resolve eq11 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = (M.op (k (M.op X0 X1) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq16
    | exact resolve eq16 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq201 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (k (M.op X1 (σ X0)) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (k (M.op X1 (σ X0)) (σ X0))
       have i₂ := eq128 X1 (σ X0)
       grind)
    | exact superpose eq128 eq36
    | exact resolve eq36 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq204 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (k (τ (M.op X1 (σ X0))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq201 X0 X1
       have i₂ := eq26 (M.op X1 (σ X0)) X0
       grind)
    | exact superpose eq26 eq201
    | exact resolve eq201 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq201
  have eq271 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X3 (M.op X4 (M.op X5 (M.op X1 (M.op X2 X0)))))) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq88 X0 X1 (M.op X1 (M.op X2 X0)) X0 X4
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq88
    | exact resolve eq88 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X2 (M.op X3 (M.op X4 (k (M.op X1 X0) X0))))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq88 X0 X1 (k (M.op X0 X1) X1) X1 X4
       have i₂ := eq129 X0 X1
       grind)
    | exact superpose eq129 eq88
    | exact resolve eq88 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq358 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq333 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq333
    | (have j0 := eq333 X0 X1
       grind)
    | exact resolve eq333 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq492 : ∀ X0 X1 X2 X3 : G, (k (M.op X3 X2) X2) = (k (M.op X3 X2) (k (M.op X0 (M.op X1 X2)) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq91 X0 X1 X2 X3 (M.op X0 (M.op X1 X2))
       have i₂ := eq29 X0 (M.op X1 X2)
       grind)
    | exact superpose eq29 eq91
    | exact resolve eq91 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq552 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq358 y x
       grind)
    | exact superpose eq358 eq110
    | (have j1 := eq358 (σ y) (σ x)
       grind)
    | (have r₁ := eq110
       have r₂ := eq358 y x
       grind)
    | exact resolve eq110 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq358
  have eq553 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq552
  have eq557 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8 (σ y) X0 (σ x)
       have i₂ := eq553
       grind)
    | exact superpose eq553 eq8
    | exact resolve eq8 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29 (σ x) (σ y)
       have i₂ := eq553
       grind)
    | exact superpose eq553 eq29
    | exact resolve eq29 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq574 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq562
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq562
    | exact resolve eq562 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq608 : ∀ X0 X1 X2 X3 : G, (k (M.op X1 (M.op X2 (k (M.op X3 X0) X0))) (M.op X2 (k (M.op X3 X0) X0))) = (k (M.op X1 (M.op X2 (k (M.op X3 X0) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq59 (k (M.op X3 X0) X0) X1 X2 X0
       have i₂ := eq129 X3 X0
       grind)
    | exact superpose eq129 eq59
    | exact resolve eq59 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq658 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq115 (τ X1) (τ X0)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq115
    | (have j0 := eq115 (τ (k X0 X1)) (τ X1)
       grind)
    | exact resolve eq115 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq695 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq658
    | (have j0 := eq658 X0 X1
       grind)
    | exact resolve eq658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq698 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq695
    | (have j0 := eq695 X0 X1
       grind)
    | exact resolve eq695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq699 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (M.op (k X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq698 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq698
    | (have j0 := eq698 X0 X1
       grind)
    | exact resolve eq698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq700 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq728 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) (M.op X2 (σ (τ (k X0 X1))))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq116 (τ X0) (τ X1) X2
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq116
    | (have j0 := eq116 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq116 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) (M.op X2 (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq728 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq728
    | (have j0 := eq728 X0 X1 X2
       grind)
    | exact resolve eq728 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq767 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (k X0 X1))) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq764 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq764
    | (have j0 := eq764 X0 X1 X2
       grind)
    | exact resolve eq764 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq768 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 (M.op X2 (k X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq767 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq767
    | (have j0 := eq767 X0 X1 X2
       grind)
    | exact resolve eq767 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq769 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (k X0 X1))) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq768 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq768
    | (have j0 := eq768 X0 X1 X2
       grind)
    | exact resolve eq768 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq796 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (k (k X0 X1) X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq128 (k X0 X1) X1
       have i₂ := eq700 X0 X1
       grind)
    | exact superpose eq700 eq128
    | (have j1 := eq700 X0 X1
       grind)
    | exact resolve eq128 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq803 : ∀ X0 X1 X2 : G, (M.op X2 (k X0 (M.op X1 X2))) = X2 ∨ (M.op X0 (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (k X0 (M.op X1 X2)) X1
       have i₂ := eq700 X0 (M.op X1 X2)
       grind)
    | exact superpose eq700 eq8
    | (have j1 := eq700 X2 (k X0 (M.op X1 X2))
       grind)
    | exact resolve eq8 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq2500 : ∀ X0 X1 X2 X3 : G, (M.op X3 (k (M.op X0 (M.op X1 (k (M.op X2 X3) X3))) (M.op X1 (k (M.op X2 X3) X3)))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq272 X3 X2 (k (M.op X0 (M.op X1 (k (M.op X2 X3) X3))) (M.op X1 (k (M.op X2 X3) X3))) X0 X1
       have i₂ := eq134 X0 (M.op X1 (k (M.op X2 X3) X3))
       grind)
    | exact superpose eq134 eq272
    | exact resolve eq272 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq272
  have eq2559 : ∀ X0 X1 X2 X3 : G, (M.op X3 (k (M.op X0 (M.op X1 (k (M.op X2 X3) X3))) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2500 X0 X1 X2 X3
       have i₂ := eq608 X3 X0 X1 X2
       grind)
    | exact superpose eq608 eq2500
    | exact resolve eq2500 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2500
  have eq2970 : (k x (τ (σ y))) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq65 x (σ y) x
       have i₂ := eq557 x
       grind)
    | exact superpose eq557 eq65
    | exact resolve eq65 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq557
  have eq3018 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2970
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2970
    | exact resolve eq2970 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2970
  have eq3334 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x x
       have i₂ := eq574
       grind)
    | exact superpose eq574 eq40
    | exact resolve eq40 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq3342 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ x)
       have i₂ := eq574
       grind)
    | exact superpose eq574 eq11
    | (have r₁ := eq11 x y
       have r₂ := eq574
       grind)
    | exact resolve eq11 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq3387 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) ≠ (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3342
       have i₂ := eq13 x x
       grind)
    | exact superpose eq13 eq3342
    | exact resolve eq3342 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342
  have eq3392 : (σ (k x y)) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3387
       have r₂ := eq3334
       grind)
    | exact resolve eq3387 eq3334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334 eq3387
  have eq3423 : (k x y) = (τ (σ (k x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq3392
       grind)
    | exact superpose eq3392 eq9
    | exact resolve eq9 eq3392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392
  have eq3474 : (k x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3423
       have i₂ := eq9 (k x x)
       grind)
    | exact superpose eq9 eq3423
    | exact resolve eq3423 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3423
  have eq3566 : ∀ X0 : G, y = (M.op y (M.op X0 (k x x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq769 x y X0
       have i₂ := eq3474
       grind)
    | exact superpose eq3474 eq769
    | (have j0 := eq769 y (M.op X0 (k x x)) x
       grind)
    | exact resolve eq769 eq3474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq3571 : ∀ X0 : G, y = (M.op y (M.op X0 (k x x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3566 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3566
  have eq3932 : ∀ X0 X1 X2 X3 : G, (k X0 (k (M.op X1 X0) X0)) = (k X0 (k (M.op X2 (M.op X3 (k (M.op X1 X0) X0))) (M.op X3 (k (M.op X1 X0) X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq492 X0 X1 (k (M.op X0 X1) X1) X1
       have i₂ := eq129 X0 X1
       grind)
    | exact superpose eq129 eq492
    | exact resolve eq492 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq492
  have eq4057 : ∀ X0 X1 X2 X3 : G, (k X0 (k (M.op X1 X0) X0)) = (k X0 (k (M.op X2 (M.op X3 (k (M.op X1 X0) X0))) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3932 X0 X1 X2 X3
       have i₂ := eq608 X0 X2 X3 X1
       grind)
    | exact superpose eq608 eq3932
    | exact resolve eq3932 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq3932
  have eq4066 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (k X0 (k (M.op X2 (M.op X3 (k (M.op X1 X0) X0))) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4057 X0 X1 X2 X3
       have i₂ := eq128 X1 X0
       grind)
    | exact superpose eq128 eq4057
    | exact resolve eq4057 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq4057
  have eq6552 : (k y (k (τ (σ x)) y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq204 y (σ x)
       have i₂ := eq553
       grind)
    | exact superpose eq553 eq204
    | exact resolve eq204 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq6561 : (k x y) = (k x (k (k x y) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq204 x (σ x)
       have i₂ := eq3018
       grind)
    | exact superpose eq3018 eq204
    | exact resolve eq204 eq3018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq6666 : (k y (k x y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6552
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq6552
    | exact resolve eq6552 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6552
  have eq7921 : (k x x) = (k x (k (k x x) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6561
       have i₂ := eq3474
       grind)
    | exact superpose eq3474 eq6561
    | exact resolve eq6561 eq3474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3474 eq6561
  have eq7944 : (k x x) = (k x (k (k x x) x)) ∨ x = (M.op x y) := by grind
  clear eq7921
  have eq8208 : (k x x) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq796 x x
       have i₂ := eq7944
       grind)
    | exact superpose eq7944 eq796
    | (have j0 := eq796 x x
       grind)
    | exact resolve eq796 eq7944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq7944
  have eq8228 : (k x x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq11 x x
       grind)
    | (have r₁ := eq8208
       have r₂ := eq11 x x
       grind)
    | (have r₁ := eq8208
       have r₂ := eq11 x y
       grind)
    | exact resolve eq8208 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8208
  have eq8343 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op x x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3571 X0
       have i₂ := eq8228
       grind)
    | exact superpose eq8228 eq3571
    | exact resolve eq3571 eq8228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3571 eq8228
  have eq8367 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op x x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8343 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8343
  have eq9521 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq88 x x x X0 y
       have i₂ := eq8367 x
       grind)
    | exact superpose eq8367 eq88
    | exact resolve eq88 eq8367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq8367
  have eq11885 : ∀ X0 X1 X2 X3 : G, (k X0 (k (M.op X1 (M.op X2 (k (M.op X3 X0) X0))) X0)) ≠ X0 ∨ (k X0 X0) = (k X0 (k (M.op X1 (M.op X2 (k (M.op X3 X0) X0))) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq131 X3 (k (M.op X0 (M.op X1 (k (M.op X2 X3) X3))) X3)
       have i₂ := eq2559 X0 X1 X2 X3
       grind)
    | exact superpose eq2559 eq131
    | exact resolve eq131 eq2559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq2559
  have eq11957 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = (k X0 (k (M.op X1 (M.op X2 (k (M.op X3 X0) X0))) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11885 X0 X1 X2 X3
       have i₂ := eq4066 X0 X3 X1 X2
       grind)
    | exact superpose eq4066 eq11885
    | (have j0 := eq11885 X0 X1 X2 X3
       grind)
    | exact resolve eq11885 eq4066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11885
  have eq11979 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq11957 X0 x x x
       have i₂ := eq4066 X0 x x x
       grind)
    | exact superpose eq4066 eq11957
    | (have j0 := eq11957 X0 x x x
       grind)
    | exact resolve eq11957 eq4066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4066 eq11957
  have eq11992 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11979 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq11979 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq11979 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11979
  have eq12045 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq11992 (σ X0)
       grind)
    | exact superpose eq11992 eq13
    | exact resolve eq13 eq11992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12054 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq11992 (τ X0)
       grind)
    | exact superpose eq11992 eq43
    | exact resolve eq43 eq11992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq12111 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12054 X0
       have i₂ := eq11992 X0
       grind)
    | exact superpose eq11992 eq12054
    | exact resolve eq12054 eq11992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12054
  have eq12117 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12045 X0
       have i₂ := eq11992 X0
       grind)
    | exact superpose eq11992 eq12045
    | exact resolve eq12045 eq11992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11992 eq12045
  have eq12475 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (τ X0) X1 (τ X0)
       have i₂ := eq12111 X0
       grind)
    | exact superpose eq12111 eq8
    | exact resolve eq8 eq12111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12111
  have eq12851 : (k x y) = (τ (σ (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3018
       have i₂ := eq12117 x
       grind)
    | exact superpose eq12117 eq3018
    | exact resolve eq3018 eq12117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018
  have eq12869 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1 (σ X0)
       have i₂ := eq12117 X0
       grind)
    | exact superpose eq12117 eq8
    | exact resolve eq8 eq12117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12871 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (σ X0) X1 (σ X0) x
       have i₂ := eq12117 X0
       grind)
    | exact superpose eq12117 eq15
    | exact resolve eq15 eq12117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq12898 : ∀ X0 X1 X2 X3 X4 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op X2 (M.op X3 (M.op X4 (σ (M.op X0 X0))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq271 (σ X0) X4 (σ X0) X1 X2 X3
       have i₂ := eq12117 X0
       grind)
    | exact superpose eq12117 eq271
    | exact resolve eq271 eq12117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq12955 : (k x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12851
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq12851
    | exact resolve eq12851 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12851
  have eq12982 : (k x y) = (M.op x x) := by
    first
    | (have j1 := eq11 x y
       grind)
    | (have r₁ := eq12955
       have r₂ := eq11 x y
       grind)
    | exact resolve eq12955 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12955
  have eq13182 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ (M.op x x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq116 x y X0
       have i₂ := eq12982
       grind)
    | exact superpose eq12982 eq116
    | (have j0 := eq116 x y x
       grind)
    | exact resolve eq116 eq12982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq13183 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq117 x y
       have i₂ := eq12982
       grind)
    | exact superpose eq12982 eq117
    | (have j0 := eq117 x y
       grind)
    | exact resolve eq117 eq12982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq14610 : ∀ X0 X2 : G, (σ X0) = (M.op (σ X0) (σ (k X2 (M.op X0 X0)))) ∨ (σ X2) = (M.op (σ X2) (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq111 X0 (M.op X0 X0) (σ X0) x
       have i₂ := eq12869 X0 x
       grind)
    | exact superpose eq12869 eq111
    | (have j0 := eq111 X0 (k X2 (M.op X0 X0)) X2 x
       grind)
    | exact resolve eq111 eq12869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq59935 : ∀ X0 : G, (τ (σ y)) = (M.op (τ (σ y)) (M.op X0 (k y (k x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12475 (σ y) X0
       have i₂ := eq6666
       grind)
    | exact superpose eq6666 eq12475
    | exact resolve eq12475 eq6666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6666 eq12475
  have eq60149 : ∀ X0 : G, (τ (σ y)) = (M.op (τ (σ y)) (M.op X0 (k y (M.op x x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59935 X0
       have i₂ := eq12982
       grind)
    | exact superpose eq12982 eq59935
    | exact resolve eq59935 eq12982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12982 eq59935
  have eq60257 : ∀ X0 : G, y = (M.op y (M.op X0 (k y (M.op x x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq60149 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq60149
    | exact resolve eq60149 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60149
  have eq61143 : y = (M.op y (M.op x x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq60257 x
       have i₂ := eq803 y x x
       grind)
    | exact superpose eq803 eq60257
    | (have j1 := eq803 y x x
       grind)
    | exact resolve eq60257 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq60257
  have eq83847 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq8 x y x
       have i₂ := eq61143
       grind)
    | exact superpose eq61143 eq8
    | exact resolve eq8 eq61143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61143
  have eq84022 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq83847
  have eq84483 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9521 y
       have i₂ := eq84022
       grind)
    | exact superpose eq84022 eq9521
    | exact resolve eq9521 eq84022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9521
  have eq84491 : ∀ X0 : G, x = (M.op x (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8 x X0 y
       have i₂ := eq84022
       grind)
    | exact superpose eq84022 eq8
    | exact resolve eq8 eq84022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84022
  have eq84614 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq84483
  have eq86383 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84491 y
       have i₂ := eq84614
       grind)
    | exact superpose eq84614 eq84491
    | exact resolve eq84491 eq84614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84491 eq84614
  have eq86563 : x = (M.op x y) := by grind
  clear eq86383
  have eq87249 : ∀ X0 : G, (M.op y y) = (k y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq30 y X0 x
       have i₂ := eq86563
       grind)
    | exact superpose eq86563 eq30
    | exact resolve eq30 eq86563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq294241 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op X0 (M.op X1 (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq12898 x X0 X1 (σ y) x
       have i₂ := eq13182 x
       grind)
    | exact superpose eq13182 eq12898
    | exact resolve eq12898 eq13182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12898 eq13182
  have eq296297 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ (M.op y y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq294241 (M.op X0 (σ (M.op y y))) x
       have i₂ := eq12871 y X0 x
       grind)
    | exact superpose eq12871 eq294241
    | exact resolve eq294241 eq12871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12871 eq294241
  have eq369038 : (σ y) = (M.op (σ y) (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ (M.op y y))) := by
    first
    | (have i₁ := eq14610 x y
       have i₂ := eq87249 x
       grind)
    | exact superpose eq87249 eq14610
    | (have j0 := eq14610 x y
       grind)
    | exact resolve eq14610 eq87249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14610 eq87249
  have eq369048 : (σ x) = (M.op (σ x) (σ (M.op y y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12869 x (σ y)
       have i₂ := eq369038
       grind)
    | exact superpose eq369038 eq12869
    | exact resolve eq12869 eq369038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12869 eq369038
  have eq369063 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq296297 (σ x)
       have i₂ := eq369048
       grind)
    | exact superpose eq369048 eq296297
    | exact resolve eq296297 eq369048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296297 eq369048
  have eq369082 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq369063
  have eq369090 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq369082
       have i₂ := eq12117 x
       grind)
    | exact superpose eq12117 eq369082
    | exact resolve eq369082 eq12117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12117 eq369082
  have eq369093 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq369090
       have r₂ := eq13183
       grind)
    | exact resolve eq369090 eq13183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13183 eq369090
  have eq369096 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq369093
       grind)
    | exact superpose eq369093 eq14
    | exact resolve eq14 eq369093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369093
  have eq369724 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq369096
       have i₂ := eq86563
       grind)
    | exact superpose eq86563 eq369096
    | exact resolve eq369096 eq86563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86563 eq369096
  have eq369725 : False := by grind
  exact eq369725

/-- `Equation617`: `x = x ◇ (x ◇ ((x ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation617 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law617 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law617.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op X0 X1) X1))) = X0 := by
    intro X0 X1
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
  have eq18 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op (M.op X0 X1) X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (M.op X0 (M.op (M.op X0 X1) X1))
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq19 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq26 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1
       have i₂ := eq12 X1 X0
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
  have eq27 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  clear eq17
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq25
    | exact resolve eq25 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq25 X1 (τ X0)
       grind)
    | exact superpose eq25 eq16
    | (have j1 := eq25 X1 (τ X0)
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq143 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq27 x y
       grind)
    | exact superpose eq27 eq14
    | (have j1 := eq27 x y
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq9
    | (have j1 := eq27 X0 X1
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X1)
       have i₂ := eq27 X1 X0
       grind)
    | exact superpose eq27 eq19
    | (have j1 := eq27 X1 X0
       grind)
    | exact resolve eq19 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq412 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq464 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq412 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq412
    | (have j0 := eq412 X0 X1
       grind)
    | exact resolve eq412 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq485 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq57
    | exact resolve eq57 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq529 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq485 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq485
    | (have j0 := eq485 X0 X1
       grind)
    | exact resolve eq485 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq572 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1
       have i₂ := eq464 X0 X1
       grind)
    | (have i₁ := eq19 X0
       have i₂ := eq464 (M.op X0 X0) X1
       grind)
    | exact superpose eq464 eq19
    | (have j1 := eq464 X0 X1
       grind)
    | exact resolve eq19 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq19 (σ X0)
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq19
    | (have j1 := eq52 X0 X0
       grind)
    | exact resolve eq19 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq937 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq143
       have i₂ := eq572 y x
       grind)
    | exact superpose eq572 eq143
    | (have j1 := eq572 y x
       grind)
    | (have r₁ := eq143
       have r₂ := eq572 y x
       grind)
    | exact resolve eq143 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq938 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq143
       have i₂ := eq529 x y
       grind)
    | exact superpose eq529 eq143
    | (have j1 := eq529 x y
       grind)
    | (have r₁ := eq143
       have r₂ := eq529 x y
       grind)
    | exact resolve eq143 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq939 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq143
       have i₂ := eq464 y x
       grind)
    | exact superpose eq464 eq143
    | (have j1 := eq464 (σ y) (σ x)
       grind)
    | (have r₁ := eq143
       have r₂ := eq464 y x
       grind)
    | exact resolve eq143 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq464
  have eq940 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq939
  have eq941 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq938
  have eq942 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq937
  have eq956 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq19 (σ x)
       have i₂ := eq940
       grind)
    | exact superpose eq940 eq19
    | exact resolve eq19 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq957 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq940
  have eq963 : (σ y) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq957
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq957
    | exact resolve eq957 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1112 : (k x y) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq963
       grind)
    | exact superpose eq963 eq9
    | exact resolve eq9 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq1151 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1112
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1112
    | exact resolve eq1112 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq1194 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq159 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq1207 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1151
       grind)
    | exact superpose eq1151 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1214 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1207
  have eq1493 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq941
  have eq1501 : (σ y) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1493
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1493
    | exact resolve eq1493 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq1561 : (k x y) = (τ (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1501
       grind)
    | exact superpose eq1501 eq9
    | exact resolve eq9 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501
  have eq1602 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1561
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1561
    | exact resolve eq1561 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561
  have eq1603 : y = (k x y) := by grind
  clear eq1602
  have eq1747 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24 y x
       have i₂ := eq1603
       grind)
    | exact superpose eq1603 eq24
    | (have j0 := eq24 y x
       grind)
    | exact resolve eq24 eq1603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1879 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq1747
  have eq2901 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq150 x x
       have i₂ := eq942
       grind)
    | exact superpose eq942 eq150
    | exact resolve eq150 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq942
  have eq2922 : x = y ∨ (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2901
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2901
    | exact resolve eq2901 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2901
  have eq2923 : (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2922
       have r₂ := eq1879
       grind)
    | exact resolve eq2922 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2922
  have eq3214 : (k x x) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq2923
       grind)
    | exact superpose eq2923 eq9
    | exact resolve eq9 eq2923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2923
  have eq3267 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3214
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3214
    | exact resolve eq3214 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3214
  have eq3308 : y = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25 x x
       have i₂ := eq3267
       grind)
    | exact superpose eq3267 eq25
    | exact resolve eq25 eq3267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3267
  have eq3314 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq3308
       have r₂ := eq1879
       grind)
    | exact resolve eq3308 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3308
  have eq3536 : x = y ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1214
       have i₂ := eq3314
       grind)
    | exact superpose eq3314 eq1214
    | exact resolve eq1214 eq3314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214 eq3314
  have eq3543 : y = (M.op x x) ∨ x = y := by grind
  clear eq3536
  have eq3883 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19 x
       have i₂ := eq3543
       grind)
    | exact superpose eq3543 eq19
    | exact resolve eq19 eq3543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3543
  have eq3890 : x = (M.op x y) := by
    first
    | (have r₁ := eq3883
       have r₂ := eq1879
       grind)
    | exact resolve eq3883 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879 eq3883
  have eq6152 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq956
       grind)
    | exact superpose eq956 eq14
    | exact resolve eq14 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq6170 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6152
       have i₂ := eq3890
       grind)
    | exact superpose eq3890 eq6152
    | exact resolve eq6152 eq3890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6152
  have eq6171 : y = (M.op x x) := by grind
  clear eq6170
  have eq6288 : x = (M.op x (M.op x y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq26 x x
       have i₂ := eq6171
       grind)
    | exact superpose eq6171 eq26
    | exact resolve eq26 eq6171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq6290 : x = (M.op x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq6288
       have i₂ := eq3890
       grind)
    | exact superpose eq3890 eq6288
    | exact resolve eq6288 eq3890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6288
  have eq6292 : y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq6290
       have i₂ := eq6171
       grind)
    | exact superpose eq6171 eq6290
    | exact resolve eq6290 eq6171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6290
  have eq9569 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1194 x y
       have i₂ := eq1603
       grind)
    | exact superpose eq1603 eq1194
    | (have j0 := eq1194 x y
       grind)
    | exact resolve eq1194 eq1603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq1603
  have eq13989 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq756 x
       have i₂ := eq6292
       grind)
    | exact superpose eq6292 eq756
    | exact resolve eq756 eq6292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq6292
  have eq14070 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq13989
       have r₂ := eq9569
       grind)
    | exact resolve eq13989 eq9569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13989
  have eq14116 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq14070
       grind)
    | exact superpose eq14070 eq14
    | exact resolve eq14 eq14070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14070
  have eq14155 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14116
       have i₂ := eq3890
       grind)
    | exact superpose eq3890 eq14116
    | exact resolve eq14116 eq3890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3890 eq14116
  have eq14156 : x = y := by grind
  clear eq14155
  have eq14212 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq14156
       grind)
    | exact superpose eq14156 eq14
    | exact resolve eq14 eq14156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14237 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9569
       have i₂ := eq14156
       grind)
    | exact superpose eq14156 eq9569
    | exact resolve eq9569 eq14156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9569
  have eq14240 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq14237
  have eq14249 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14212
       have i₂ := eq6171
       grind)
    | exact superpose eq6171 eq14212
    | exact resolve eq14212 eq6171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6171 eq14212
  have eq14251 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq14249
       have i₂ := eq14240
       grind)
    | exact superpose eq14240 eq14249
    | exact resolve eq14249 eq14240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14240 eq14249
  have eq14252 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq14251
       have i₂ := eq14156
       grind)
    | exact superpose eq14156 eq14251
    | exact resolve eq14251 eq14156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14156 eq14251
  have eq14253 : False := by grind
  exact eq14253

/-- `Equation617`: `x = x ◇ (x ◇ ((x ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pyx_pxy_Equation617 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law617 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law617.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op X0 X1) X1))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op (M.op X0 X1) X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (M.op X0 (M.op (M.op X0 X1) X1))
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 X0 x
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq22
    | exact resolve eq22 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq42 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  clear eq17
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq163 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq40 x y
       grind)
    | exact superpose eq40 eq14
    | (have j1 := eq40 x y
       grind)
    | exact resolve eq14 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq201 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq63 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq234 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq201 (σ X0)
       grind)
    | exact superpose eq201 eq13
    | exact resolve eq13 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq234 X0
       have i₂ := eq201 X0
       grind)
    | exact superpose eq201 eq234
    | exact resolve eq234 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq234
  have eq388 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (σ X0)
       have i₂ := eq245 X0
       grind)
    | exact superpose eq245 eq23
    | exact resolve eq23 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq733 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq653 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq653
    | (have j0 := eq653 X0 X1
       grind)
    | exact resolve eq653 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq1048 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq163
       have i₂ := eq733 y x
       grind)
    | exact superpose eq733 eq163
    | (have j1 := eq733 (σ y) (σ x)
       grind)
    | (have r₁ := eq163
       have r₂ := eq733 y x
       grind)
    | exact resolve eq163 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq733
  have eq1049 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1048
  have eq1054 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1049
       have i₂ := eq245 x
       grind)
    | exact superpose eq245 eq1049
    | exact resolve eq1049 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq1049
  have eq1310 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq1054
       grind)
    | exact superpose eq1054 eq9
    | exact resolve eq9 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq1347 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1310
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1310
    | exact resolve eq1310 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq1348 : y = (M.op x x) := by grind
  clear eq1347
  have eq1560 : x = (M.op x y) := by
    first
    | (have i₁ := eq23 x
       have i₂ := eq1348
       grind)
    | exact superpose eq1348 eq23
    | exact resolve eq23 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq1562 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq388 x
       have i₂ := eq1348
       grind)
    | exact superpose eq1348 eq388
    | exact resolve eq388 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq1348
  have eq2057 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1562
       grind)
    | exact superpose eq1562 eq14
    | exact resolve eq14 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562
  have eq2064 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2057
       have i₂ := eq1560
       grind)
    | exact superpose eq1560 eq2057
    | exact resolve eq2057 eq1560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560 eq2057
  have eq2065 : False := by grind
  exact eq2065

/-- `Equation618`: `x = x ◇ (x ◇ ((x ◇ y) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation618 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law618 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law618.models_iff G M).mp hM
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
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X1 X1
       grind)
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
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
  have eq386 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq387 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq386 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq394 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq387 (σ X0) (σ X1)
       grind)
    | exact superpose eq387 eq13
    | exact resolve eq13 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq394 X0 X1
       have i₂ := eq387 X0 X1
       grind)
    | exact superpose eq387 eq394
    | exact resolve eq394 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq394
  have eq1404 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq409 x y
       grind)
    | exact superpose eq409 eq14
    | (have r₁ := eq14
       have r₂ := eq409 x y
       grind)
    | exact resolve eq14 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq1422 : False := by grind
  exact eq1422
