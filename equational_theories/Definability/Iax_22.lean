import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4297`: `x ◇ (x ◇ y) = y ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pyy_pxy_Equation4297 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4297 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4297.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X3 X3)) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X2 X0) X3
       have i₂ := eq8 X2 X0 X1
       grind)
    | (have i₁ := eq8 X1 (M.op X2 X2) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 X2) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq8 X0 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 x X0 X3
       have i₂ := eq8 x X0 X1
       grind)
    | (have i₁ := eq8 x x x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X2 X1 x
       grind)
    | (have i₁ := eq8 X0 X1 X1
       have i₂ := eq8 X1 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq60 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op X1 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    grind
  have eq63 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X2 (k X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    grind
  have eq65 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 (k (τ X0) X1) X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq34
    | exact resolve eq34 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op X3 (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 X0)
       have i₂ := eq24 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq8 X2 X3 (M.op X0 X0)
       have i₂ := eq24 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq24 eq8
    | exact resolve eq8 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28 X2 (M.op X3 X3) X1
       have i₂ := eq8 X0 X1 X3
       grind)
    | (have i₁ := eq28 X0 (M.op X0 X1) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq28
    | exact resolve eq28 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq174 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = (k X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X2 X1
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq60 X1 X1
       have i₂ := eq8 X1 X1 X2
       grind)
    | exact superpose eq8 eq60
    | exact resolve eq60 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (k X1 (σ (M.op (τ X1) (τ X1)))) = (σ (M.op X0 (M.op X0 (M.op (τ X1) (τ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op (τ X1) (τ X1))
       have i₂ := eq60 (τ X1) X0
       grind)
    | exact superpose eq60 eq16
    | exact resolve eq16 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq228 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 (k X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X0
       have i₂ := eq63 X1 X0 X0
       grind)
    | exact superpose eq63 eq60
    | exact resolve eq60 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq63
  have eq358 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq462 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = (M.op X0 (M.op X1 (M.op X4 X4))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq22 X1 X4 X0 x
       have i₂ := eq22 X1 X2 X0 x
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq721 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op X3 (M.op X0 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op x x)
       have i₂ := eq23 X1 X0 x x
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq1705 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq358 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq1781 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1705 (σ X0)
       grind)
    | exact superpose eq1705 eq13
    | exact resolve eq13 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1783 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0 X0
       have i₂ := eq1705 (τ X0)
       grind)
    | exact superpose eq1705 eq46
    | exact resolve eq46 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1790 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1783 X0
       have i₂ := eq1705 X0
       grind)
    | exact superpose eq1705 eq1783
    | exact resolve eq1783 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783
  have eq1792 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1781 X0
       have i₂ := eq1705 X0
       grind)
    | exact superpose eq1705 eq1781
    | exact resolve eq1781 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705 eq1781
  have eq1957 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X1))) = (k (τ X0) (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq174 X2 X1 (τ X0)
       have i₂ := eq1790 X0
       grind)
    | exact superpose eq1790 eq174
    | exact resolve eq174 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790
  have eq1982 : ∀ X0 X1 X2 : G, (τ (k X0 (M.op X0 X0))) = (M.op X1 (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1957 X0 X1 X2
       have i₂ := eq46 (M.op X0 X0) X0
       grind)
    | exact superpose eq46 eq1957
    | exact resolve eq1957 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq2061 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  clear eq43
  have eq2133 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2061 X0 X1
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq2061
    | (have j0 := eq2061 X0 X1
       grind)
    | exact resolve eq2061 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061
  have eq2202 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2133 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq2133
    | (have j0 := eq2133 X0 X1
       grind)
    | exact resolve eq2133 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133
  have eq2269 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (σ X0)
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq8
    | exact resolve eq8 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2277 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2 (σ X0)
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq24
    | exact resolve eq24 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3962 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2277 (σ X0) X1 X2
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq2277
    | exact resolve eq2277 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq14827 : ∀ X0 X1 : G, (M.op (k X1 (M.op X1 X1)) X0) = (k (k X1 (M.op X1 X1)) X0) ∨ (M.op (k X1 (M.op X1 X1)) X0) = (k (k X1 (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq228 (k X1 (M.op X1 X1)) X1
       have i₂ := eq12 (k X1 (M.op X1 X1)) X1
       grind)
    | (have i₁ := eq228 X0 X1
       have i₂ := eq12 X0 (M.op X0 (k X1 (M.op X1 X1)))
       grind)
    | exact superpose eq12 eq228
    | (have j1 := eq12 (k X1 (M.op X1 X1)) X0
       grind)
    | exact resolve eq228 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq14931 : ∀ X0 X1 : G, (M.op (k X1 (M.op X1 X1)) X0) = (k (k X1 (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq14827 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14827
  have eq26928 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2202 x y
       grind)
    | exact superpose eq2202 eq14
    | (have j1 := eq2202 x y
       grind)
    | exact resolve eq14 eq2202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202
  have eq27429 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26928
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq26928
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq26928 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26928
  have eq27435 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq27429
  have eq27436 : y = (M.op x x) := by grind
  clear eq27435
  have eq27673 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq8
    | exact resolve eq8 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27679 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1 x
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq24
    | exact resolve eq24 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq27699 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op (M.op X2 X2) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq111 X2 x X0 X1
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq111
    | exact resolve eq111 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq27722 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq462 X0 X1 X2 x
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq462
    | exact resolve eq462 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq27752 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2269 x X0 X1
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq2269
    | exact resolve eq2269 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq27753 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2277 x X0 X1
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq2277
    | exact resolve eq2277 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277
  have eq27779 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq144 x x X0 X1
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq144
    | exact resolve eq144 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq27781 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq174 x x X0
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq174
    | exact resolve eq174 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq27786 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq721 x x X0 X1
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq721
    | exact resolve eq721 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq27788 : ∀ X0 : G, (τ (k X0 (M.op X0 X0))) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1982 X0 x x
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq1982
    | exact resolve eq1982 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982 eq27436
  have eq27833 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq27722 X0 X1 x
       have i₂ := eq27753 X1 x
       grind)
    | exact superpose eq27753 eq27722
    | exact resolve eq27722 eq27753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27722
  have eq27850 : ∀ X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) y)) = (M.op X1 (σ y)) := by
    intro X1 X2
    first
    | (have i₁ := eq27699 x X1 X2
       have i₂ := eq27752 x X1
       grind)
    | exact superpose eq27752 eq27699
    | exact resolve eq27699 eq27752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27699
  have eq35877 : ∀ X0 X1 : G, (M.op X0 (σ (σ (M.op X1 X1)))) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq3962 X1 X0 X0
       have i₂ := eq27673 X0 X0
       grind)
    | exact superpose eq27673 eq3962
    | exact resolve eq3962 eq27673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52167 : ∀ X0 X1 X2 : G, (M.op X1 (σ (σ (M.op X2 X2)))) = (M.op X1 (M.op (M.op X0 X0) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3962 X2 X1 (M.op X0 X0)
       have i₂ := eq27679 (M.op X0 X0) X0
       grind)
    | exact superpose eq27679 eq3962
    | exact resolve eq3962 eq27679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3962 eq27679
  have eq52290 : ∀ X1 X2 : G, (M.op X1 (σ (σ (M.op X2 X2)))) = (M.op X1 (σ y)) := by
    intro X1 X2
    first
    | (have i₁ := eq52167 x X1 X2
       have i₂ := eq27850 X1 x
       grind)
    | exact superpose eq27850 eq52167
    | exact resolve eq52167 eq27850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27850 eq52167
  have eq52670 : ∀ X1 : G, (M.op X1 y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq52290 X1 x
       have i₂ := eq35877 X1 x
       grind)
    | exact superpose eq35877 eq52290
    | exact resolve eq52290 eq35877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35877 eq52290
  have eq56146 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq52670 (σ x)
       grind)
    | exact superpose eq52670 eq14
    | exact resolve eq14 eq52670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134979 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 (M.op (τ X0) (τ X0)))) (τ X2)) = (τ (k (k X0 (σ (M.op (τ X0) (τ X0)))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 (M.op X1 (M.op X1 (M.op (τ X0) (τ X0)))) X2
       have i₂ := eq185 X1 X0
       grind)
    | exact superpose eq185 eq34
    | exact resolve eq34 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq185
  have eq134998 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 (M.op (τ X0) (τ X0)))) (τ X2)) = (k (k (τ X0) (M.op (τ X0) (τ X0))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134979 X0 X1 X2
       have i₂ := eq65 X0 (M.op (τ X0) (τ X0)) X2
       grind)
    | exact superpose eq65 eq134979
    | exact resolve eq134979 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq134979
  have eq135201 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 (M.op (τ X0) (τ X0)))) (τ X2)) = (M.op (k (τ X0) (M.op (τ X0) (τ X0))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134998 X0 X1 X2
       have i₂ := eq14931 (τ X2) (τ X0)
       grind)
    | exact superpose eq14931 eq134998
    | exact resolve eq134998 eq14931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134998
  have eq135395 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op x y)) (τ X2)) = (k (M.op X1 (M.op X1 (M.op (τ X0) (τ X0)))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135201 X0 X1 X2
       have i₂ := eq27781 (τ X0)
       grind)
    | exact superpose eq27781 eq135201
    | exact resolve eq135201 eq27781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135201
  have eq135579 : ∀ X2 : G, (M.op (M.op x (M.op x y)) (τ X2)) = (k (M.op x (M.op x y)) (τ X2)) := by
    intro X2
    first
    | (have i₁ := eq135395 x x X2
       have i₂ := eq27779 x (τ x)
       grind)
    | exact superpose eq27779 eq135395
    | exact resolve eq135395 eq27779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27779 eq135395
  have eq135740 : ∀ X2 : G, (M.op (M.op y (σ y)) (τ X2)) = (k (M.op y (σ y)) (τ X2)) := by
    intro X2
    first
    | (have i₁ := eq135579 X2
       have i₂ := eq27752 x y
       grind)
    | exact superpose eq27752 eq135579
    | exact resolve eq135579 eq27752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135579
  have eq135891 : ∀ X2 : G, (M.op (M.op y y) (τ X2)) = (k (M.op y y) (τ X2)) := by
    intro X2
    first
    | (have i₁ := eq135740 X2
       have i₂ := eq52670 y
       grind)
    | exact superpose eq52670 eq135740
    | exact resolve eq135740 eq52670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135740
  have eq340913 : ∀ X0 X1 : G, (τ (k (k X0 (M.op X0 X0)) X1)) = (k (M.op x (M.op x y)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 (k X0 (M.op X0 X0))
       have i₂ := eq27788 X0
       grind)
    | exact superpose eq27788 eq46
    | exact resolve eq46 eq27788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq27788
  have eq340915 : ∀ X0 X1 : G, (τ (k (k X0 (M.op X0 X0)) X1)) = (k (M.op y (σ y)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq340913 X0 X1
       have i₂ := eq27752 x y
       grind)
    | exact superpose eq27752 eq340913
    | exact resolve eq340913 eq27752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340913
  have eq340990 : ∀ X0 X1 : G, (k (M.op y y) (τ X1)) = (τ (k (k X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq340915 X0 X1
       have i₂ := eq52670 y
       grind)
    | exact superpose eq52670 eq340915
    | exact resolve eq340915 eq52670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340915
  have eq341065 : ∀ X0 X1 : G, (k (M.op y y) (τ X1)) = (τ (M.op (k X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq340990 X0 X1
       have i₂ := eq14931 X1 X0
       grind)
    | exact superpose eq14931 eq340990
    | exact resolve eq340990 eq14931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14931 eq340990
  have eq341136 : ∀ X1 : G, (k (M.op y y) (τ X1)) = (τ (M.op (M.op x (M.op x y)) X1)) := by
    intro X1
    first
    | (have i₁ := eq341065 x X1
       have i₂ := eq27781 x
       grind)
    | exact superpose eq27781 eq341065
    | exact resolve eq341065 eq27781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27781 eq341065
  have eq341187 : ∀ X1 : G, (k (M.op y y) (τ X1)) = (τ (M.op (M.op y (σ y)) X1)) := by
    intro X1
    first
    | (have i₁ := eq341136 X1
       have i₂ := eq27752 x y
       grind)
    | exact superpose eq27752 eq341136
    | exact resolve eq341136 eq27752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341136
  have eq341228 : ∀ X1 : G, (k (M.op y y) (τ X1)) = (τ (M.op (M.op y y) X1)) := by
    intro X1
    first
    | (have i₁ := eq341187 X1
       have i₂ := eq52670 y
       grind)
    | exact superpose eq52670 eq341187
    | exact resolve eq341187 eq52670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341187
  have eq341257 : ∀ X1 : G, (M.op (M.op y y) (τ X1)) = (τ (M.op (M.op y y) X1)) := by
    intro X1
    first
    | (have i₁ := eq341228 X1
       have i₂ := eq135891 X1
       grind)
    | exact superpose eq135891 eq341228
    | exact resolve eq341228 eq135891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135891 eq341228
  have eq563820 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (M.op y y) (τ (M.op (M.op y y) X0))) := by
    intro X0
    first
    | (have i₁ := eq341257 (M.op (M.op y y) X0)
       have i₂ := eq27673 (M.op y y) X0
       grind)
    | exact superpose eq27673 eq341257
    | exact resolve eq341257 eq27673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27673
  have eq563944 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (M.op y y) (M.op (M.op y y) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq563820 X0
       have i₂ := eq341257 X0
       grind)
    | exact superpose eq341257 eq563820
    | exact resolve eq563820 eq341257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341257 eq563820
  have eq564013 : ∀ X0 : G, (M.op (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq563944 X0
       have i₂ := eq27786 (M.op y y) (τ X0)
       grind)
    | exact superpose eq27786 eq563944
    | exact resolve eq563944 eq27786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27786 eq563944
  have eq564072 : ∀ X0 : G, (M.op (τ X0) (M.op y (σ y))) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq564013 X0
       have i₂ := eq27752 x y
       grind)
    | exact superpose eq27752 eq564013
    | exact resolve eq564013 eq27752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27752 eq564013
  have eq564123 : ∀ X0 : G, (M.op (τ X0) (M.op y y)) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq564072 X0
       have i₂ := eq27833 (τ X0) y
       grind)
    | exact superpose eq27833 eq564072
    | exact resolve eq564072 eq27833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27833 eq564072
  have eq564165 : ∀ X0 : G, (M.op (τ X0) (σ y)) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq564123 X0
       have i₂ := eq27753 (τ X0) y
       grind)
    | exact superpose eq27753 eq564123
    | exact resolve eq564123 eq27753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27753 eq564123
  have eq564186 : ∀ X0 : G, (M.op (τ X0) y) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq564165 X0
       have i₂ := eq52670 (τ X0)
       grind)
    | exact superpose eq52670 eq564165
    | exact resolve eq564165 eq52670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52670 eq564165
  have eq567288 : ∀ X0 : G, (M.op X0 y) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 y)
       have i₂ := eq564186 X0
       grind)
    | exact superpose eq564186 eq10
    | exact resolve eq10 eq564186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564186
  have eq569280 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq567288 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq567288
    | exact resolve eq567288 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567288
  have eq570319 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq56146
       have i₂ := eq569280 x
       grind)
    | exact superpose eq569280 eq56146
    | (have r₁ := eq56146
       have r₂ := eq569280 x
       grind)
    | exact resolve eq56146 eq569280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56146 eq569280
  have eq570329 : False := by grind
  exact eq570329

/-- `Equation430`: `x = x ◇ (y ◇ (x ◇ (y ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation430 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law430 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X1 X1)))) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq18 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq18 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq26 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq34 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
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
  have eq134 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq26 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq26
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq153 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq9
    | (have j1 := eq26 X0 X1
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X1)
       have i₂ := eq26 X1 X0
       grind)
    | exact superpose eq26 eq18
    | (have j1 := eq26 X1 X0
       grind)
    | exact resolve eq18 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq447 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq504 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq447
    | (have j0 := eq447 X0 X1
       grind)
    | exact resolve eq447 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq554 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq555 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1
       have i₂ := eq504 X0 X1
       grind)
    | (have i₁ := eq18 X0
       have i₂ := eq504 (M.op X0 X0) X1
       grind)
    | exact superpose eq504 eq18
    | (have j1 := eq504 X0 X1
       grind)
    | exact resolve eq18 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18 (σ X0)
       have i₂ := eq51 X0 X0
       grind)
    | exact superpose eq51 eq18
    | (have j1 := eq51 X0 X0
       grind)
    | exact resolve eq18 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1042 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq146
       have i₂ := eq555 y x
       grind)
    | exact superpose eq555 eq146
    | (have j1 := eq555 y x
       grind)
    | (have r₁ := eq146
       have r₂ := eq555 y x
       grind)
    | exact resolve eq146 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq1043 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq146
       have i₂ := eq554 y x
       grind)
    | exact superpose eq554 eq146
    | (have j1 := eq554 y x
       grind)
    | (have r₁ := eq146
       have r₂ := eq554 y x
       grind)
    | exact resolve eq146 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq1044 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq146
       have i₂ := eq504 y x
       grind)
    | exact superpose eq504 eq146
    | (have j1 := eq504 (σ y) (σ x)
       grind)
    | (have r₁ := eq146
       have r₂ := eq504 y x
       grind)
    | exact resolve eq146 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq504
  have eq1045 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1044
  have eq1046 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq1043
  have eq1047 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1042
  have eq1062 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  have eq1063 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18 (σ x)
       have i₂ := eq1045
       grind)
    | exact superpose eq1045 eq18
    | exact resolve eq18 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1070 : (σ y) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1062
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1062
    | exact resolve eq1062 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1101 : (k x y) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1070
       grind)
    | exact superpose eq1070 eq9
    | exact resolve eq9 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1138 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1101
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1101
    | exact resolve eq1101 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1189 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1138
       grind)
    | exact superpose eq1138 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq1196 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1189
  have eq1324 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq162 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq1354 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq134 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq134
    | (have j0 := eq134 X1 (τ X0)
       grind)
    | exact resolve eq134 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq1448 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1354 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1354
    | (have j0 := eq1354 X0 X1
       grind)
    | exact resolve eq1354 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1354
  have eq1456 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1448 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1448
    | (have j0 := eq1448 X0 X1
       grind)
    | exact resolve eq1448 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448
  have eq1602 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq1046
  have eq1611 : (σ y) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1602
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1602
    | exact resolve eq1602 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602
  have eq1743 : (k x y) = (τ (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1611
       grind)
    | exact superpose eq1611 eq9
    | exact resolve eq9 eq1611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1611
  have eq1786 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1743
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1743
    | exact resolve eq1743 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq1787 : y = (k x y) := by grind
  clear eq1786
  have eq1824 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22 y x
       have i₂ := eq1787
       grind)
    | exact superpose eq1787 eq22
    | (have j0 := eq22 y x
       grind)
    | exact resolve eq22 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1899 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq1824
  have eq2308 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq153 x x
       have i₂ := eq1047
       grind)
    | exact superpose eq1047 eq153
    | exact resolve eq153 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1047
  have eq2334 : x = y ∨ (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2308
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2308
    | exact resolve eq2308 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2308
  have eq2335 : (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2334
       have r₂ := eq1899
       grind)
    | exact resolve eq2334 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2334
  have eq2488 : (k x x) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq2335
       grind)
    | exact superpose eq2335 eq9
    | exact resolve eq9 eq2335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335
  have eq2532 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2488
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2488
    | exact resolve eq2488 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2488
  have eq2815 : y = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24 x x
       have i₂ := eq2532
       grind)
    | exact superpose eq2532 eq24
    | exact resolve eq24 eq2532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2532
  have eq2825 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq2815
       have r₂ := eq1899
       grind)
    | exact resolve eq2815 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2815
  have eq3017 : x = y ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1196
       have i₂ := eq2825
       grind)
    | exact superpose eq2825 eq1196
    | exact resolve eq1196 eq2825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196 eq2825
  have eq3026 : y = (M.op x x) ∨ x = y := by grind
  clear eq3017
  have eq3274 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18 x
       have i₂ := eq3026
       grind)
    | exact superpose eq3026 eq18
    | exact resolve eq18 eq3026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3026
  have eq3287 : x = (M.op x y) := by
    first
    | (have r₁ := eq3274
       have r₂ := eq1899
       grind)
    | exact resolve eq3274 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899 eq3274
  have eq5143 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1063
       grind)
    | exact superpose eq1063 eq14
    | exact resolve eq14 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq5158 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5143
       have i₂ := eq3287
       grind)
    | exact superpose eq3287 eq5143
    | exact resolve eq5143 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5143
  have eq5159 : y = (M.op x x) := by grind
  clear eq5158
  have eq12751 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1324 x y
       have i₂ := eq1787
       grind)
    | exact superpose eq1787 eq1324
    | (have j0 := eq1324 x y
       grind)
    | exact resolve eq1324 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq12952 : y = (M.op x y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1787
       have i₂ := eq1456 x y
       grind)
    | exact superpose eq1456 eq1787
    | (have j1 := eq1456 x y
       grind)
    | exact resolve eq1787 eq1456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456 eq1787
  have eq13072 : x = y ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq12952
       have i₂ := eq3287
       grind)
    | exact superpose eq3287 eq12952
    | exact resolve eq12952 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12952
  have eq13073 : y = (k x x) ∨ x = y := by grind
  clear eq13072
  have eq17730 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq841 x
       have i₂ := eq13073
       grind)
    | exact superpose eq13073 eq841
    | exact resolve eq841 eq13073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq13073
  have eq17822 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq17730
       have r₂ := eq12751
       grind)
    | exact resolve eq17730 eq12751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17730
  have eq17875 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq17822
       grind)
    | exact superpose eq17822 eq14
    | exact resolve eq14 eq17822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17822
  have eq17920 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq17875
       have i₂ := eq3287
       grind)
    | exact superpose eq3287 eq17875
    | exact resolve eq17875 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3287 eq17875
  have eq17921 : x = y := by grind
  clear eq17920
  have eq17977 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17921
       grind)
    | exact superpose eq17921 eq14
    | exact resolve eq14 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18005 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12751
       have i₂ := eq17921
       grind)
    | exact superpose eq17921 eq12751
    | exact resolve eq12751 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12751
  have eq18008 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq18005
  have eq18016 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17977
       have i₂ := eq5159
       grind)
    | exact superpose eq5159 eq17977
    | exact resolve eq17977 eq5159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5159 eq17977
  have eq18018 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq18016
       have i₂ := eq18008
       grind)
    | exact superpose eq18008 eq18016
    | exact resolve eq18016 eq18008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18008 eq18016
  have eq18021 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq18018
       have i₂ := eq17921
       grind)
    | exact superpose eq17921 eq18018
    | exact resolve eq18018 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17921 eq18018
  have eq18022 : False := by grind
  exact eq18022

/-- `Equation430`: `x = x ◇ (y ◇ (x ◇ (y ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pyx_pxy_Equation430 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law430 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X1 X1)))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq22 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq166 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq39 x y
       grind)
    | exact superpose eq39 eq14
    | (have j1 := eq39 x y
       grind)
    | exact resolve eq14 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq202 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq62 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq243 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq202 (σ X0)
       grind)
    | exact superpose eq202 eq13
    | exact resolve eq13 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq243 X0
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq243
    | exact resolve eq243 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq243
  have eq369 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0)
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq22
    | exact resolve eq22 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1077 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq166
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq166
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq166 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq1078 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1077
  have eq1082 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1078
       have i₂ := eq254 x
       grind)
    | exact superpose eq254 eq1078
    | exact resolve eq1078 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq1078
  have eq1090 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq1082
       grind)
    | exact superpose eq1082 eq9
    | exact resolve eq9 eq1082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1126 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1090
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1090
    | exact resolve eq1090 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1127 : y = (M.op x x) := by grind
  clear eq1126
  have eq1280 : x = (M.op x y) := by
    first
    | (have i₁ := eq22 x
       have i₂ := eq1127
       grind)
    | exact superpose eq1127 eq22
    | exact resolve eq22 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1284 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq369 x
       have i₂ := eq1127
       grind)
    | exact superpose eq1127 eq369
    | exact resolve eq369 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq1127
  have eq1707 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1284
       grind)
    | exact superpose eq1284 eq14
    | exact resolve eq14 eq1284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1713 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1707
       have i₂ := eq1280
       grind)
    | exact superpose eq1280 eq1707
    | exact resolve eq1707 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280 eq1707
  have eq1714 : False := by grind
  exact eq1714

/-- `Equation4301`: `x ◇ (x ◇ y) = z ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation4301 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4301 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4301.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X0 X2) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq8 X0 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | (have i₁ := eq8 X0 X0 x
       have i₂ := eq8 X0 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X1 X3) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 (M.op X1 X3)
       have i₂ := eq8 X1 X3 X0
       grind)
    | (have i₁ := eq8 X2 X1 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 X2) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq8 X0 X1 (M.op X0 X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X0 X2 x
       grind)
    | (have i₁ := eq8 X1 X1 X1
       have i₂ := eq8 X1 X1 X2
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
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X1 X2)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
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
  clear eq17
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X1 X2) X3
       have i₂ := eq20 X2 X1 X0
       grind)
    | (have i₁ := eq8 X2 (M.op X1 X2) X3
       have i₂ := eq20 X0 X1 X2
       grind)
    | exact superpose eq20 eq8
    | exact resolve eq8 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq99 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X2 X3 (M.op X1 X2)
       have i₂ := eq20 X2 X1 X0
       grind)
    | (have i₁ := eq25 X2 X3 (M.op X1 X2)
       have i₂ := eq20 X0 X1 X2
       grind)
    | exact superpose eq20 eq25
    | exact resolve eq25 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X2 X3 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq25 X0 X1 (M.op X0 X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq25
    | exact resolve eq25 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq128 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq44
  have eq138 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq33
    | exact resolve eq33 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq33 X1 (τ X0)
       grind)
    | exact superpose eq33 eq16
    | (have j1 := eq33 X1 (τ X0)
       grind)
    | exact resolve eq16 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq145 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq259 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op X2 (M.op X3 X0)) ∨ (M.op X3 X0) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X3 X3 X2 X1
       have i₂ := eq12 X3 X0
       grind)
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 (M.op X2 X0)
       have i₂ := eq22 X0 X2 X3 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X3 X4 X2 (M.op X0 X2)
       have i₂ := eq22 X2 X0 X1 X2
       grind)
    | exact superpose eq22 eq19
    | exact resolve eq19 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq551 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 X3 (M.op X0 X3)
       have i₂ := eq22 X3 X0 X1 X3
       grind)
    | exact superpose eq22 eq20
    | exact resolve eq20 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq72 X3 X4 X2 (M.op X0 X2)
       have i₂ := eq22 X2 X0 X1 X2
       grind)
    | exact superpose eq22 eq72
    | exact resolve eq72 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq865 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X2)) = (M.op (M.op X3 (M.op X3 X4)) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 X2 (M.op X3 X0) (M.op X3 (M.op X3 X4))
       have i₂ := eq23 X3 X4 X0 X1
       grind)
    | exact superpose eq23 eq20
    | exact resolve eq20 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq23
  have eq974 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq72 X3 X4 X2 X2
       have i₂ := eq551 X2 X2 X0 X1
       grind)
    | (have i₁ := eq72 X0 X1 X3 X2
       have i₂ := eq551 X0 X1 X2 X3
       grind)
    | exact superpose eq551 eq72
    | exact resolve eq72 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq977 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq72 X1 x X1 X0
       have i₂ := eq551 X1 (M.op x X1) X2 X3
       grind)
    | (have i₁ := eq72 X3 X1 (M.op X1 X3) X3
       have i₂ := eq551 X0 X1 (M.op X1 X3) X3
       grind)
    | exact superpose eq551 eq72
    | exact resolve eq72 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1492 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq35 X1 X1 X0
       grind)
    | exact superpose eq35 eq12
    | (have j0 := eq12 X1 (k X1 X1)
       have j1 := eq35 X2 X1 X2
       grind)
    | exact resolve eq12 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1606 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op X2 (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq35 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq35 eq13
    | (have j1 := eq35 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq13 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1856 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X2 (M.op X3 X2)) ∨ (M.op X2 (M.op X3 X2)) = (k X0 (M.op X2 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq145 X0 (M.op X2 (M.op X3 X2))
       have i₂ := eq99 X2 X3 X0 X1
       grind)
    | (have i₁ := eq145 X2 (M.op X2 X3)
       have i₂ := eq99 X0 X1 X2 X3
       grind)
    | exact superpose eq99 eq145
    | (have j0 := eq145 X0 (M.op X2 (M.op X3 X2))
       grind)
    | (have r₁ := eq145 X2 (M.op X2 (M.op X0 (M.op X1 X0)))
       have r₂ := eq99 X0 X1 X2 (M.op X0 (M.op X1 X0))
       grind)
    | (have r₁ := eq145 X3 (M.op X3 (M.op X3 X3))
       have r₂ := eq99 X3 X3 X3 X3
       grind)
    | exact resolve eq145 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1865 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (k X0 (M.op X2 (M.op X3 X2))) := by
    intro X0 X2 X3
    first
    | (have j0 := eq1856 X0 x X2 X3
       grind)
    | (have r₁ := eq1856 X0 x X2 X3
       have r₂ := eq551 X0 x X2 X3
       grind)
    | (have r₁ := eq1856 X3 X3 x x
       have r₂ := eq551 x x X3 X3
       grind)
    | exact resolve eq1856 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1856
  have eq2092 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X2 (M.op X2 X3)) ∨ (M.op X2 (M.op X2 X3)) = (k X0 (M.op X2 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq145 X0 (M.op X2 (M.op X2 X3))
       have i₂ := eq100 X2 X3 X0 X1
       grind)
    | (have i₁ := eq145 X2 (M.op X2 X3)
       have i₂ := eq100 X0 X1 X2 X3
       grind)
    | exact superpose eq100 eq145
    | (have j0 := eq145 X0 (M.op X2 (M.op X2 X3))
       grind)
    | (have r₁ := eq145 X2 (M.op X2 (M.op X2 X3))
       have r₂ := eq100 X2 X3 X2 X3
       grind)
    | (have r₁ := eq145 X2 (M.op X2 (M.op X0 (M.op X0 X1)))
       have r₂ := eq100 X0 X1 X2 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq145 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq2163 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (k X0 (M.op X2 (M.op X2 X3))) := by
    intro X0 X2 X3
    first
    | (have j0 := eq2092 X0 x X2 X3
       grind)
    | (have r₁ := eq2092 X0 x X2 X3
       have r₂ := eq546 X0 x X2 X3
       grind)
    | (have r₁ := eq2092 X2 X3 X0 x
       have r₂ := eq546 X0 x X2 X3
       grind)
    | exact resolve eq2092 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2092
  have eq2188 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq2266 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq36 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq3108 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X3 (M.op X4 (M.op X5 X4))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq72 X4 X5 X3 X3
       have i₂ := eq549 X3 X3 X0 X1 X2
       grind)
    | (have i₁ := eq72 X0 X1 X3 (M.op X3 X4)
       have i₂ := eq549 X0 X1 (M.op X3 X4) X3 X4
       grind)
    | exact superpose eq549 eq72
    | exact resolve eq72 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq549
  have eq6696 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (k X3 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1865 X0 X1 X3
       have i₂ := eq35 (M.op X3 X1) X1 x
       grind)
    | (have i₁ := eq1865 X0 x X1
       have i₂ := eq35 X0 X1 x
       grind)
    | exact superpose eq35 eq1865
    | (have j1 := eq35 X1 X0 x
       grind)
    | exact resolve eq1865 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1865
  have eq16314 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
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
  clear eq39
  have eq16478 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16314 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq16314
    | (have j0 := eq16314 X0 X1
       grind)
    | exact resolve eq16314 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16314
  have eq16502 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq144 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq144
    | exact resolve eq144 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq16611 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16502 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq16502
    | (have j0 := eq16502 X0 X1
       grind)
    | exact resolve eq16502 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16502
  have eq17220 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq546 X2 X3 (σ X0) (σ X1)
       have i₂ := eq138 X0 X1
       grind)
    | exact superpose eq138 eq546
    | (have j1 := eq138 X0 X1
       grind)
    | exact resolve eq546 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq77390 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq2188
       have i₂ := eq16611 x y
       grind)
    | exact superpose eq16611 eq2188
    | (have j1 := eq16611 x y
       grind)
    | (have r₁ := eq2188
       have r₂ := eq16611 x y
       grind)
    | exact resolve eq2188 eq16611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16611
  have eq77391 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2188
       have i₂ := eq16478 y x
       grind)
    | exact superpose eq16478 eq2188
    | (have j1 := eq16478 (σ y) (σ x)
       grind)
    | (have r₁ := eq2188
       have r₂ := eq16478 y x
       grind)
    | exact resolve eq2188 eq16478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188 eq16478
  have eq77392 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq77391
  have eq77393 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq77390
  have eq77404 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq128 x
       have i₂ := eq77392
       grind)
    | exact superpose eq77392 eq128
    | exact resolve eq128 eq77392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77572 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77404
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq77404
    | exact resolve eq77404 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77404
  have eq79070 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq77572
       grind)
    | exact superpose eq77572 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq77572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77572
  have eq79075 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq79070
  have eq80925 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1 x y
       have i₂ := eq79075
       grind)
    | exact superpose eq79075 eq546
    | exact resolve eq546 eq79075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80927 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq551 x y X0 X1
       have i₂ := eq79075
       grind)
    | exact superpose eq79075 eq551
    | exact resolve eq551 eq79075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84923 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (k x y) := by
    first
    | (have i₁ := eq128 x
       have i₂ := eq77393
       grind)
    | exact superpose eq77393 eq128
    | exact resolve eq128 eq77393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq77393
  have eq85098 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq84923
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq84923
    | exact resolve eq84923 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84923
  have eq85099 : y = (k x y) := by grind
  clear eq85098
  have eq93634 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq80925 X0 (M.op X0 x)
       have i₂ := eq80925 X0 x
       grind)
    | exact superpose eq80925 eq80925
    | exact resolve eq80925 eq80925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93792 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80925 (σ x) (σ x)
       have i₂ := eq77392
       grind)
    | exact superpose eq77392 eq80925
    | exact resolve eq80925 eq77392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77392 eq80925
  have eq94468 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq93792
  have eq94469 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq93634 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93634
  have eq96907 : y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80927 y x
       have i₂ := eq79075
       grind)
    | exact superpose eq79075 eq80927
    | exact resolve eq80927 eq79075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80927
  have eq97597 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq96907
  have eq100122 : y ≠ y ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq145 y y
       have i₂ := eq97597
       grind)
    | exact superpose eq97597 eq145
    | (have j0 := eq145 y y
       grind)
    | (have r₁ := eq145 y y
       have r₂ := eq97597
       grind)
    | exact resolve eq145 eq97597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq97597
  have eq100258 : y = (k y y) ∨ y = (M.op x x) := by grind
  clear eq100122
  have eq102835 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2266 y
       have i₂ := eq100258
       grind)
    | exact superpose eq100258 eq2266
    | (have j0 := eq2266 y
       grind)
    | exact resolve eq2266 eq100258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100258
  have eq102841 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq102835
  have eq142121 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq94468
       grind)
    | exact superpose eq94468 eq14
    | exact resolve eq14 eq94468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94468
  have eq145037 : y ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq142121
       have i₂ := eq79075
       grind)
    | exact superpose eq79075 eq142121
    | exact resolve eq142121 eq79075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142121
  have eq145040 : y ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq145037
  have eq153518 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq94469 X0
       have i₂ := eq79075
       grind)
    | exact superpose eq79075 eq94469
    | exact resolve eq94469 eq79075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79075 eq94469
  have eq153983 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq153518 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153518
  have eq157155 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 y) ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq546 X0 X1 X2 y
       have i₂ := eq153983 X2
       grind)
    | exact superpose eq153983 eq546
    | exact resolve eq546 eq153983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq196046 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq153983 x
       have i₂ := eq157155 X0 X1 x
       grind)
    | exact superpose eq157155 eq153983
    | exact resolve eq153983 eq157155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153983 eq157155
  have eq196361 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq196046 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196046
  have eq200074 : y = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq196361 (σ y) (σ y)
       have i₂ := eq102841
       grind)
    | exact superpose eq102841 eq196361
    | exact resolve eq196361 eq102841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196361
  have eq201088 : y = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq200074
  have eq222159 : y = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq102841
       have i₂ := eq201088
       grind)
    | exact superpose eq201088 eq102841
    | exact resolve eq102841 eq201088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102841 eq201088
  have eq222462 : y = (σ y) ∨ y = (M.op x x) := by grind
  clear eq222159
  have eq222465 : y = (M.op x x) := by
    first
    | (have r₁ := eq222462
       have r₂ := eq145040
       grind)
    | exact resolve eq222462 eq145040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145040 eq222462
  have eq226650 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 y) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq259 x X1 x x
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq259
    | exact resolve eq259 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq226742 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq551 X0 X1 x x
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq551
    | exact resolve eq551 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq226743 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq553 X0 X1 X2 x x
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq553
    | exact resolve eq553 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq226800 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq974 X0 X1 X2 x x
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq974
    | exact resolve eq974 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq226802 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq977 X0 X1 x x
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq977
    | exact resolve eq977 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq226813 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2163 X0 x x
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq2163
    | exact resolve eq2163 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2163
  have eq226817 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X3 (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3108 X0 X1 X2 X3 x x
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq3108
    | exact resolve eq3108 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3108
  have eq226818 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) := by
    intro X2
    first
    | (have i₁ := eq226800 x x X2
       have i₂ := eq226802 x x
       grind)
    | exact superpose eq226802 eq226800
    | exact resolve eq226800 eq226802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226800
  have eq226844 : ∀ X1 : G, (M.op x y) = (M.op X1 y) ∨ y = (k x x) := by
    intro X1
    first
    | (have i₁ := eq226650 x X1
       have i₂ := eq226802 x X1
       grind)
    | exact superpose eq226802 eq226650
    | exact resolve eq226650 eq226802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226650
  have eq230904 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) X1)) = X0 ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq865 X2 (M.op X2 x) X1 X2 x
       have i₂ := eq1492 (M.op X2 (M.op X2 x)) X2 X0
       grind)
    | (have i₁ := eq865 X0 X1 X2 x x
       have i₂ := eq1492 X0 X1 (M.op (M.op x (M.op x x)) (M.op X0 (M.op X0 X1)))
       grind)
    | exact superpose eq1492 eq865
    | (have j1 := eq1492 X0 X2 X0
       grind)
    | exact resolve eq865 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq1492
  have eq231028 : ∀ X0 X2 : G, (M.op X2 X2) = (k X2 X2) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op x y) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq230904 X0 x X2
       have i₂ := eq226802 x (M.op X2 X2)
       grind)
    | exact superpose eq226802 eq230904
    | (have j0 := eq230904 X2 x X2
       grind)
    | exact resolve eq230904 eq226802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230904
  have eq241343 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2266 (M.op x y)
       have i₂ := eq226813 (M.op x y)
       grind)
    | exact superpose eq226813 eq2266
    | (have j0 := eq2266 (M.op x y)
       grind)
    | exact resolve eq2266 eq226813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226813
  have eq241368 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq241343
  have eq290716 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op X2 (M.op (σ X0) X2)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1606 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606
  have eq290717 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op x y) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq290716 X0 X1 x
       have i₂ := eq226802 x (σ X0)
       grind)
    | exact superpose eq226802 eq290716
    | (have j0 := eq290716 X0 X1 x
       grind)
    | exact resolve eq290716 eq226802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226802 eq290716
  have eq291930 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ y = (k x x) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq226844 X0
       have i₂ := eq226844 X1
       grind)
    | (have i₁ := eq226844 X1
       have i₂ := eq226844 x
       grind)
    | exact superpose eq226844 eq226844
    | exact resolve eq226844 eq226844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226844
  have eq292638 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have j0 := eq291930 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291930
  have eq533190 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq226743 (σ (M.op x y)) (σ (M.op x y)) X0
       have i₂ := eq241368
       grind)
    | exact superpose eq241368 eq226743
    | exact resolve eq226743 eq241368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226743
  have eq533198 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq226817 X0 (σ (M.op x y)) (σ (M.op x y)) X1
       have i₂ := eq241368
       grind)
    | exact superpose eq241368 eq226817
    | exact resolve eq226817 eq241368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226817
  have eq533203 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq533198 X0 X1
       have i₂ := eq241368
       grind)
    | exact superpose eq241368 eq533198
    | exact resolve eq533198 eq241368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533198
  have eq533210 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq533190 X0
       have i₂ := eq241368
       grind)
    | exact superpose eq241368 eq533190
    | exact resolve eq533190 eq241368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241368 eq533190
  have eq533379 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq533203 X0 x
       have i₂ := eq226818 x
       grind)
    | exact superpose eq226818 eq533203
    | exact resolve eq533203 eq226818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533203
  have eq533382 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq533210 x
       have i₂ := eq226818 x
       grind)
    | exact superpose eq226818 eq533210
    | exact resolve eq533210 eq226818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226818 eq533210
  have eq546105 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 (σ (M.op X0 y))) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq533379 X0
       have i₂ := eq292638 X0 x
       grind)
    | (have i₁ := eq533379 X0
       have i₂ := eq292638 x X1
       grind)
    | exact superpose eq292638 eq533379
    | exact resolve eq533379 eq292638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292638 eq533379
  have eq666214 : ∀ X0 X1 : G, (M.op x y) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq290717 (τ X1) (τ X0)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq290717
    | exact resolve eq290717 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq290717
  have eq666246 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op x y) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq666214 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq666214
    | (have j0 := eq666214 X0 X1
       grind)
    | exact resolve eq666214 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666214
  have eq666252 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq666246 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq666246
    | (have j0 := eq666246 X0 X1
       grind)
    | exact resolve eq666246 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666246
  have eq666258 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq666252 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq666252
    | (have j0 := eq666252 X0 X1
       grind)
    | exact resolve eq666252 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666252
  have eq666260 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op x y) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq666258 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq666258
    | (have j0 := eq666258 X0 X1
       grind)
    | exact resolve eq666258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666258
  have eq828061 : y = (M.op x y) ∨ (M.op x x) = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq85099
       have i₂ := eq231028 y x
       grind)
    | exact superpose eq231028 eq85099
    | (have j1 := eq231028 x x
       grind)
    | exact resolve eq85099 eq231028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85099 eq231028
  have eq828069 : y = (M.op x y) ∨ (M.op x x) = (k x x) := by grind
  clear eq828061
  have eq828080 : y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq828069
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq828069
    | exact resolve eq828069 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828069
  have eq847928 : ∀ X0 : G, y = (k X0 y) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq6696 x x x
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq6696
    | exact resolve eq6696 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6696
  have eq848080 : ∀ X0 : G, y ≠ (M.op x y) ∨ y = (M.op X0 y) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq666260 X0 y
       have i₂ := eq847928 X0
       grind)
    | exact superpose eq847928 eq666260
    | exact resolve eq666260 eq847928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666260 eq847928
  have eq848170 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (k x x) := by
    intro X0
    first
    | (have j0 := eq848080 X0
       grind)
    | (have r₁ := eq848080 X0
       have r₂ := eq828080
       grind)
    | exact resolve eq848080 eq828080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848080
  have eq848450 : ∀ X1 : G, y = (M.op X1 (σ y)) ∨ y = (k x x) ∨ y = (k x x) := by
    intro X1
    first
    | (have i₁ := eq546105 x X1
       have i₂ := eq848170 x
       grind)
    | exact superpose eq848170 eq546105
    | exact resolve eq546105 eq848170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546105 eq848170
  have eq849056 : ∀ X1 : G, y = (M.op X1 (σ y)) ∨ y = (k x x) := by
    intro X1
    first
    | (have j0 := eq848450 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848450
  have eq850561 : y ≠ (σ (M.op x y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq849056 (σ x)
       grind)
    | exact superpose eq849056 eq14
    | exact resolve eq14 eq849056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849056
  have eq850577 : y ≠ (M.op x y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq850561
       have i₂ := eq533382
       grind)
    | exact superpose eq533382 eq850561
    | exact resolve eq850561 eq533382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850561
  have eq850908 : y = (k x x) := by
    first
    | (have r₁ := eq850577
       have r₂ := eq828080
       grind)
    | exact resolve eq850577 eq828080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828080 eq850577
  have eq851212 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2266 x
       have i₂ := eq850908
       grind)
    | exact superpose eq850908 eq2266
    | (have j0 := eq2266 x
       grind)
    | exact resolve eq2266 eq850908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266
  have eq854606 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq17220 x x x x
       have i₂ := eq850908
       grind)
    | exact superpose eq850908 eq17220
    | exact resolve eq17220 eq850908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17220 eq850908
  have eq854885 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq854606 x x
       have i₂ := eq226742 x x
       grind)
    | exact superpose eq226742 eq854606
    | exact resolve eq854606 eq226742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226742 eq854606
  have eq857116 : (M.op x y) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq854885
       grind)
    | exact superpose eq854885 eq14
    | exact resolve eq14 eq854885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854885
  have eq857446 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq857116
       have r₂ := eq533382
       grind)
    | exact resolve eq857116 eq533382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857116
  have eq857518 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq857446
       grind)
    | exact superpose eq857446 eq14
    | exact resolve eq14 eq857446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq857540 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq851212
       have i₂ := eq857446
       grind)
    | exact superpose eq857446 eq851212
    | (have r₁ := eq851212
       have r₂ := eq857446
       grind)
    | exact resolve eq851212 eq857446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851212
  have eq857541 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq857446
       grind)
    | exact superpose eq857446 eq9
    | exact resolve eq9 eq857446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857446
  have eq857622 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq857540
  have eq857651 : x = y := by
    first
    | (have i₁ := eq857541
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq857541
    | exact resolve eq857541 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857541
  have eq857652 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq857518
       have i₂ := eq857622
       grind)
    | exact superpose eq857622 eq857518
    | exact resolve eq857518 eq857622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857518 eq857622
  have eq857656 : (M.op x y) ≠ (σ x) := by
    first
    | (have i₁ := eq857652
       have i₂ := eq533382
       grind)
    | exact superpose eq533382 eq857652
    | exact resolve eq857652 eq533382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857652
  have eq857660 : (σ x) ≠ (M.op x x) := by
    first
    | (have i₁ := eq857656
       have i₂ := eq857651
       grind)
    | exact superpose eq857651 eq857656
    | exact resolve eq857656 eq857651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857656
  have eq857664 : y ≠ (σ x) := by
    first
    | (have i₁ := eq857660
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq857660
    | exact resolve eq857660 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857660
  have eq857668 : x ≠ (σ x) := by
    first
    | (have i₁ := eq857664
       have i₂ := eq857651
       grind)
    | exact superpose eq857651 eq857664
    | exact resolve eq857664 eq857651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857664
  have eq857831 : (M.op x x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq533382
       have i₂ := eq857651
       grind)
    | exact superpose eq857651 eq533382
    | exact resolve eq533382 eq857651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533382
  have eq857902 : y = (σ y) := by
    first
    | (have i₁ := eq857831
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq857831
    | exact resolve eq857831 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222465 eq857831
  have eq858016 : x = (σ x) := by
    first
    | (have i₁ := eq857902
       have i₂ := eq857651
       grind)
    | exact superpose eq857651 eq857902
    | exact resolve eq857902 eq857651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857651 eq857902
  have eq858053 : False := by grind
  exact eq858053

/-- `Equation4301`: `x ◇ (x ◇ y) = z ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pyx_pxy_Equation4301 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4301 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4301.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
    intro X0 X1 X2
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
  have eq24 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | (have i₁ := eq8 X0 X0 x
       have i₂ := eq8 X0 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X1 X3) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 (M.op X1 X3)
       have i₂ := eq8 X1 X3 X0
       grind)
    | (have i₁ := eq8 X2 X1 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq55 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X1 X2) X3
       have i₂ := eq24 X2 X1 X0
       grind)
    | (have i₁ := eq8 X2 (M.op X1 X2) X3
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq8
    | exact resolve eq8 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq691 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X2 X3 (M.op X0 X3)
       have i₂ := eq26 X3 X0 X1 X3
       grind)
    | exact superpose eq26 eq24
    | exact resolve eq24 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq26
  have eq1157 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq95 X3 X4 X2 X2
       have i₂ := eq691 X2 X2 X0 X1
       grind)
    | (have i₁ := eq95 X0 X1 X3 X2
       have i₂ := eq691 X0 X1 X2 X3
       grind)
    | exact superpose eq691 eq95
    | exact resolve eq95 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1162 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq95 X1 x X1 X0
       have i₂ := eq691 X1 (M.op x X1) X2 X3
       grind)
    | (have i₁ := eq95 X3 X1 (M.op X1 X3) X3
       have i₂ := eq691 X0 X1 (M.op X1 X3) X3
       grind)
    | exact superpose eq691 eq95
    | exact resolve eq95 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq691
  have eq2460 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq52 x y
       grind)
    | exact superpose eq52 eq14
    | (have j1 := eq52 x y
       grind)
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq3591 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq417 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq3614 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq3591 (σ X0)
       grind)
    | exact superpose eq3591 eq13
    | exact resolve eq13 eq3591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3625 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3614 X0
       have i₂ := eq3591 X0
       grind)
    | exact superpose eq3591 eq3614
    | exact resolve eq3614 eq3591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3591 eq3614
  have eq3840 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1162 X1 X2 (σ X0) (σ X0)
       have i₂ := eq3625 X0
       grind)
    | exact superpose eq3625 eq1162
    | exact resolve eq1162 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18634 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq18842 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18634 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq18634
    | (have j0 := eq18634 X0 X1
       grind)
    | exact resolve eq18634 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18634
  have eq82558 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2460
       have i₂ := eq18842 y x
       grind)
    | exact superpose eq18842 eq2460
    | (have j1 := eq18842 (σ y) (σ x)
       grind)
    | (have r₁ := eq2460
       have r₂ := eq18842 y x
       grind)
    | exact resolve eq2460 eq18842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460 eq18842
  have eq82559 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq82558
  have eq82563 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82559
       have i₂ := eq3625 x
       grind)
    | exact superpose eq3625 eq82559
    | exact resolve eq82559 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82559
  have eq82571 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq82563
       grind)
    | exact superpose eq82563 eq9
    | exact resolve eq9 eq82563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82563
  have eq82615 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82571
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq82571
    | exact resolve eq82571 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82571
  have eq82616 : y = (M.op x x) := by grind
  clear eq82615
  have eq82827 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3840 x X0 X1
       have i₂ := eq82616
       grind)
    | exact superpose eq82616 eq3840
    | exact resolve eq3840 eq82616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82956 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1157 X0 X1 X2 x x
       have i₂ := eq82616
       grind)
    | exact superpose eq82616 eq1157
    | exact resolve eq1157 eq82616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq82958 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1162 X0 X1 x x
       have i₂ := eq82616
       grind)
    | exact superpose eq82616 eq1162
    | exact resolve eq1162 eq82616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq82616
  have eq82972 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) := by
    intro X2
    first
    | (have i₁ := eq82956 x x X2
       have i₂ := eq82958 x x
       grind)
    | exact superpose eq82958 eq82956
    | exact resolve eq82956 eq82958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82956
  have eq82996 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq82827 x x
       have i₂ := eq82958 x x
       grind)
    | exact superpose eq82958 eq82827
    | exact resolve eq82827 eq82958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82827
  have eq92827 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq3840 (M.op x y) X0 X1
       have i₂ := eq82972 (M.op x y)
       grind)
    | exact superpose eq82972 eq3840
    | exact resolve eq3840 eq82972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3840
  have eq93152 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (σ (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq92827 X0 X1
       have i₂ := eq3625 (M.op x y)
       grind)
    | exact superpose eq3625 eq92827
    | exact resolve eq92827 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3625 eq92827
  have eq93218 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq93152 X0 X1
       have i₂ := eq82972 (M.op x y)
       grind)
    | exact superpose eq82972 eq93152
    | exact resolve eq93152 eq82972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82972 eq93152
  have eq93253 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq93218 x x
       have i₂ := eq82958 x x
       grind)
    | exact superpose eq82958 eq93218
    | exact resolve eq93218 eq82958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82958 eq93218
  have eq100236 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq82996
       grind)
    | exact superpose eq82996 eq14
    | exact resolve eq14 eq82996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82996
  have eq100504 : False := by grind
  exact eq100504

/-- `Equation4301`: `x ◇ (x ◇ y) = z ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4301 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4301 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4301.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X0 X2) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq8 X0 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | (have i₁ := eq8 X0 X0 x
       have i₂ := eq8 X0 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X1 X3) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 (M.op X1 X3)
       have i₂ := eq8 X1 X3 X0
       grind)
    | (have i₁ := eq8 X2 X1 (M.op X0 X2)
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
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq34 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq37 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq40 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq45 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq74 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq144 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq34 (τ X1) X0
       grind)
    | exact superpose eq34 eq17
    | (have j1 := eq34 (τ X1) X0
       grind)
    | exact resolve eq17 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq34 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq45
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
  have eq443 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 (M.op X2 X0)
       have i₂ := eq22 X0 X2 X3 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 X3 (M.op X0 X3)
       have i₂ := eq22 X3 X0 X1 X3
       grind)
    | exact superpose eq22 eq20
    | exact resolve eq20 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq450 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    grind
  have eq465 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq167 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq167 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq167
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq167 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op X3 X0) ∨ (M.op X3 X0) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq443 X1 X2 X3 X3
       have i₂ := eq12 X3 X0
       grind)
    | (have i₁ := eq443 X0 X1 X2 X3
       have i₂ := eq12 X0 (M.op X2 X3)
       grind)
    | exact superpose eq12 eq443
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq443 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X4) (M.op X5 (M.op X2 X5))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq22 X5 X2 x X4
       have i₂ := eq443 X2 x X0 X1
       grind)
    | (have i₁ := eq22 X5 X2 x X4
       have i₂ := eq443 X0 X1 X2 x
       grind)
    | exact superpose eq443 eq22
    | exact resolve eq22 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq443
  have eq984 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X3 X4 X2 X2
       have i₂ := eq448 X2 X2 X0 X1
       grind)
    | (have i₁ := eq19 X0 X1 X3 X2
       have i₂ := eq448 X0 X1 X2 X3
       grind)
    | exact superpose eq448 eq19
    | exact resolve eq19 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq989 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 x X1 X0
       have i₂ := eq448 X1 (M.op X1 x) X2 X3
       grind)
    | (have i₁ := eq19 X3 X1 (M.op X3 X1) X3
       have i₂ := eq448 X0 X1 (M.op X3 X1) X3
       grind)
    | exact superpose eq448 eq19
    | exact resolve eq19 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1715 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq37 x y
       grind)
    | exact superpose eq37 eq14
    | (have j1 := eq37 x y
       grind)
    | exact resolve eq14 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1748 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq9
    | (have j1 := eq37 X0 X1
       grind)
    | exact resolve eq9 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1789 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq37 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq16958 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1789 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1789
    | (have j0 := eq1789 (τ X0)
       grind)
    | exact resolve eq1789 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq16960 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq16958 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16958
    | (have j0 := eq16958 X0
       grind)
    | exact resolve eq16958 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16958
  have eq16963 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16960 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16960
    | (have j0 := eq16960 X0
       grind)
    | exact resolve eq16960 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16960
  have eq17001 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq40
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq17181 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17001 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq17001
    | (have j0 := eq17001 X0 X1
       grind)
    | exact resolve eq17001 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17001
  have eq17202 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq16963 (τ X0)
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq16963
    | (have j0 := eq16963 (τ X0)
       grind)
    | exact resolve eq16963 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq16963
  have eq17204 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq144 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq144
    | exact resolve eq144 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq17245 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17204 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq17204
    | (have j0 := eq17204 X0 X1
       grind)
    | exact resolve eq17204 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17204
  have eq90397 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1715
       have i₂ := eq17245 y x
       grind)
    | exact superpose eq17245 eq1715
    | (have j1 := eq17245 y x
       grind)
    | (have r₁ := eq1715
       have r₂ := eq17245 y x
       grind)
    | exact resolve eq1715 eq17245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17245
  have eq90398 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1715
       have i₂ := eq17181 y x
       grind)
    | exact superpose eq17181 eq1715
    | (have j1 := eq17181 (σ y) (σ x)
       grind)
    | (have r₁ := eq1715
       have r₂ := eq17181 y x
       grind)
    | exact resolve eq1715 eq17181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715
  have eq90399 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq90398
  have eq90400 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq90397
  have eq90410 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq90399
       grind)
    | exact superpose eq90399 eq167
    | exact resolve eq167 eq90399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90598 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq90410
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq90410
    | exact resolve eq90410 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90410
  have eq90691 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq90598
       grind)
    | exact superpose eq90598 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq90598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90694 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq17181 y x
       have i₂ := eq90598
       grind)
    | exact superpose eq90598 eq17181
    | (have j0 := eq17181 y x
       grind)
    | exact resolve eq17181 eq90598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90598
  have eq90695 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq90694
  have eq90696 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq90691
  have eq92426 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0 X1 y x
       have i₂ := eq90696
       grind)
    | exact superpose eq90696 eq448
    | exact resolve eq448 eq90696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92448 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 X1 y x
       have i₂ := eq90696
       grind)
    | exact superpose eq90696 eq989
    | exact resolve eq989 eq90696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98198 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq90400
       grind)
    | exact superpose eq90400 eq167
    | exact resolve eq167 eq90400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90400
  have eq98392 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq98198
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq98198
    | exact resolve eq98198 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98198
  have eq98393 : x = (k x y) := by grind
  clear eq98392
  have eq98454 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1748 x x
       have i₂ := eq90399
       grind)
    | exact superpose eq90399 eq1748
    | exact resolve eq1748 eq90399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748
  have eq98721 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq98454
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq98454
    | exact resolve eq98454 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98454
  have eq114612 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92426 (σ x) (σ x)
       have i₂ := eq90399
       grind)
    | exact superpose eq90399 eq92426
    | exact resolve eq92426 eq90399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92426
  have eq115370 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq114612
  have eq135986 : (σ (M.op x y)) ≠ (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq115370
       grind)
    | exact superpose eq115370 eq14
    | exact resolve eq14 eq115370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115370
  have eq138927 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq135986
       have i₂ := eq90695
       grind)
    | exact superpose eq90695 eq135986
    | exact resolve eq135986 eq90695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90695 eq135986
  have eq138928 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq138927
  have eq182890 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq17202 (σ X0)
       have i₂ := eq465 (σ X0) X0
       grind)
    | exact superpose eq465 eq17202
    | (have j0 := eq17202 (σ X0)
       have j1 := eq465 (σ X0) X0
       grind)
    | exact resolve eq17202 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq182911 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq182890 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq182890
    | (have j0 := eq182890 X0
       grind)
    | exact resolve eq182890 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182890
  have eq182919 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq182911 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq182911
    | (have j0 := eq182911 X0
       grind)
    | exact resolve eq182911 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182911
  have eq182921 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq182919 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq182919
    | (have j0 := eq182919 X0
       grind)
    | exact resolve eq182919 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182919
  have eq182923 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq182921 X0
       have j1 := eq147 X0 X0
       grind)
    | (have r₁ := eq182921 x
       have r₂ := eq147 x x
       grind)
    | exact resolve eq182921 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq182921
  have eq186041 : x ≠ (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq182923 x
       have i₂ := eq90399
       grind)
    | exact superpose eq90399 eq182923
    | (have j0 := eq182923 x
       grind)
    | exact resolve eq182923 eq90399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90399 eq182923
  have eq186058 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq186041
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq186041
    | exact resolve eq186041 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186041
  have eq203636 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq98721
       grind)
    | exact superpose eq98721 eq9
    | exact resolve eq9 eq98721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98721
  have eq203685 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq203636
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq203636
    | exact resolve eq203636 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203636
  have eq207156 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34 x x
       have i₂ := eq203685
       grind)
    | exact superpose eq203685 eq34
    | exact resolve eq34 eq203685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq203685
  have eq207164 : y = (M.op x x) ∨ x = y := by grind
  clear eq207156
  have eq211012 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq450 x x
       have i₂ := eq207164
       grind)
    | exact superpose eq207164 eq450
    | exact resolve eq450 eq207164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207164
  have eq228339 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq211012
       have i₂ := eq90696
       grind)
    | exact superpose eq90696 eq211012
    | exact resolve eq211012 eq90696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90696 eq211012
  have eq228372 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq228339
       have r₂ := eq186058
       grind)
    | exact resolve eq228339 eq186058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186058 eq228339
  have eq231288 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1789 x
       have i₂ := eq228372
       grind)
    | exact superpose eq228372 eq1789
    | (have j0 := eq1789 x
       grind)
    | exact resolve eq1789 eq228372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789 eq228372
  have eq231304 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq231288
  have eq249796 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92448 (σ x) (σ x)
       have i₂ := eq231304
       grind)
    | exact superpose eq231304 eq92448
    | exact resolve eq92448 eq231304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92448
  have eq249799 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq249796
  have eq430981 : (σ x) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq231304
       have i₂ := eq249799
       grind)
    | exact superpose eq249799 eq231304
    | exact resolve eq231304 eq249799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231304 eq249799
  have eq431411 : (σ x) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq430981
  have eq431424 : y = (M.op x x) := by
    first
    | (have r₁ := eq431411
       have r₂ := eq138928
       grind)
    | exact resolve eq431411 eq138928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138928 eq431411
  have eq435995 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0 X1 x x
       have i₂ := eq431424
       grind)
    | exact superpose eq431424 eq448
    | exact resolve eq448 eq431424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq435996 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq450 x x
       have i₂ := eq431424
       grind)
    | exact superpose eq431424 eq450
    | exact resolve eq450 eq431424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq436064 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x X2) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq714 X0 X1 x X2 x
       have i₂ := eq431424
       grind)
    | exact superpose eq431424 eq714
    | exact resolve eq714 eq431424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq436092 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq984 X0 X1 X2 x x
       have i₂ := eq431424
       grind)
    | exact superpose eq431424 eq984
    | exact resolve eq984 eq431424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq436094 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 X1 x x
       have i₂ := eq431424
       grind)
    | exact superpose eq431424 eq989
    | exact resolve eq989 eq431424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq436155 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) := by
    intro X2
    first
    | (have i₁ := eq436092 x x X2
       have i₂ := eq436094 x x
       grind)
    | exact superpose eq436094 eq436092
    | exact resolve eq436092 eq436094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436092 eq436094
  have eq461861 : (τ (M.op x y)) ≠ (τ (M.op x y)) ∨ (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
    first
    | (have i₁ := eq17202 (M.op x y)
       have i₂ := eq435996
       grind)
    | exact superpose eq435996 eq17202
    | (have j0 := eq17202 (M.op x y)
       grind)
    | exact resolve eq17202 eq435996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17202 eq435996
  have eq461871 : (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by grind
  clear eq461861
  have eq636808 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq436064 (τ (M.op x y)) (τ (M.op x y)) X0
       have i₂ := eq461871
       grind)
    | exact superpose eq461871 eq436064
    | exact resolve eq436064 eq461871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436064
  have eq636827 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (τ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq636808 X0
       have i₂ := eq461871
       grind)
    | exact superpose eq461871 eq636808
    | exact resolve eq636808 eq461871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461871 eq636808
  have eq636972 : (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq636827 x
       have i₂ := eq436155 (M.op x x)
       grind)
    | exact superpose eq436155 eq636827
    | exact resolve eq636827 eq436155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636827
  have eq639292 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq636972
       grind)
    | exact superpose eq636972 eq10
    | exact resolve eq10 eq636972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661856 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq660 (σ y) X0 X1 (σ x)
       grind)
    | exact superpose eq660 eq14
    | (have j1 := eq660 (σ y) X1 x (σ x)
       grind)
    | exact resolve eq14 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq661917 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op x y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq661856 X0 X1
       have i₂ := eq639292
       grind)
    | exact superpose eq639292 eq661856
    | exact resolve eq661856 eq639292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661856
  have eq662018 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq661917 x x
       have r₂ := eq435995 x x
       grind)
    | exact resolve eq661917 eq435995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661917
  have eq662046 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq662018
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq662018
    | exact resolve eq662018 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662018
  have eq662052 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq662046
       have i₂ := eq98393
       grind)
    | exact superpose eq98393 eq662046
    | exact resolve eq662046 eq98393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98393 eq662046
  have eq662069 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq662052
       grind)
    | exact superpose eq662052 eq14
    | exact resolve eq14 eq662052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662436 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq435995 (σ x) (σ y)
       have i₂ := eq662052
       grind)
    | exact superpose eq662052 eq435995
    | exact resolve eq435995 eq662052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662659 : (M.op x y) ≠ (σ x) := by
    first
    | (have i₁ := eq662069
       have i₂ := eq639292
       grind)
    | exact superpose eq639292 eq662069
    | exact resolve eq662069 eq639292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662069
  have eq664950 : x = (k x (τ (M.op x y))) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq662436
       grind)
    | exact superpose eq662436 eq167
    | exact resolve eq167 eq662436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq662436
  have eq665451 : x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq664950
       have i₂ := eq636972
       grind)
    | exact superpose eq636972 eq664950
    | exact resolve eq664950 eq636972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636972 eq664950
  have eq666160 : (σ x) = (σ (M.op x (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq17181 (M.op x y) x
       have i₂ := eq665451
       grind)
    | exact superpose eq665451 eq17181
    | (have j0 := eq17181 (M.op x y) x
       grind)
    | exact resolve eq17181 eq665451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17181 eq665451
  have eq666165 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq666160
       have i₂ := eq435995 x y
       grind)
    | exact superpose eq435995 eq666160
    | exact resolve eq666160 eq435995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435995 eq666160
  have eq666179 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq666165
       have i₂ := eq639292
       grind)
    | exact superpose eq639292 eq666165
    | exact resolve eq666165 eq639292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666165
  have eq666187 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq666179
       have r₂ := eq662659
       grind)
    | exact resolve eq666179 eq662659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666179
  have eq666189 : y = (M.op x y) := by
    first
    | (have i₁ := eq666187
       have i₂ := eq431424
       grind)
    | exact superpose eq431424 eq666187
    | exact resolve eq666187 eq431424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431424 eq666187
  have eq666929 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq436155 x
       have i₂ := eq666189
       grind)
    | exact superpose eq666189 eq436155
    | exact resolve eq436155 eq666189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436155
  have eq666943 : y = (σ y) := by
    first
    | (have i₁ := eq639292
       have i₂ := eq666189
       grind)
    | exact superpose eq666189 eq639292
    | exact resolve eq639292 eq666189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639292
  have eq666948 : y ≠ (σ x) := by
    first
    | (have i₁ := eq662659
       have i₂ := eq666189
       grind)
    | exact superpose eq666189 eq662659
    | exact resolve eq662659 eq666189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662659 eq666189
  have eq670340 : (σ x) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq662052
       have i₂ := eq666943
       grind)
    | exact superpose eq666943 eq662052
    | exact resolve eq662052 eq666943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662052 eq666943
  have eq670433 : y = (σ x) := by
    first
    | (have i₁ := eq670340
       have i₂ := eq666929 (σ x)
       grind)
    | exact superpose eq666929 eq670340
    | exact resolve eq670340 eq666929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666929 eq670340
  have eq670457 : False := by grind
  exact eq670457

/-- `Equation4301`: `x ◇ (x ◇ y) = z ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pyx_Equation4301 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4301 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4301.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X0 X2) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq8 X0 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | (have i₁ := eq8 X0 X0 x
       have i₂ := eq8 X0 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X1 X3) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 (M.op X1 X3)
       have i₂ := eq8 X1 X3 X0
       grind)
    | (have i₁ := eq8 X2 X1 (M.op X0 X2)
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
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq34 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X1 X2)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X1 X2
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq36 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq74 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq77 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq29
  have eq84 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq77
    | exact resolve eq77 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq131 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq44
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq140 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq32
    | exact resolve eq32 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op X2 (M.op X3 X0)) ∨ (M.op X3 X0) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X3 X3 X2 X1
       have i₂ := eq12 X0 X3
       grind)
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X0 X3
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 (M.op X2 X0)
       have i₂ := eq22 X0 X2 X3 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 X3 (M.op X0 X3)
       have i₂ := eq22 X3 X0 X1 X3
       grind)
    | exact superpose eq22 eq20
    | exact resolve eq20 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq452 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    grind
  have eq717 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X4) (M.op X5 (M.op X2 X5))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq22 X5 X2 x X4
       have i₂ := eq445 X2 x X0 X1
       grind)
    | (have i₁ := eq22 X5 X2 x X4
       have i₂ := eq445 X0 X1 X2 x
       grind)
    | exact superpose eq445 eq22
    | exact resolve eq22 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq987 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X3 X4 X2 X2
       have i₂ := eq450 X2 X2 X0 X1
       grind)
    | (have i₁ := eq19 X0 X1 X3 X2
       have i₂ := eq450 X0 X1 X2 X3
       grind)
    | exact superpose eq450 eq19
    | exact resolve eq19 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq992 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 x X1 X0
       have i₂ := eq450 X1 (M.op X1 x) X2 X3
       grind)
    | (have i₁ := eq19 X3 X1 (M.op X3 X1) X3
       have i₂ := eq450 X0 X1 (M.op X3 X1) X3
       grind)
    | exact superpose eq450 eq19
    | exact resolve eq19 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1718 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq14
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1751 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq9
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1792 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq16963 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1792 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1792
    | (have j0 := eq1792 (τ X0)
       grind)
    | exact resolve eq1792 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq16965 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq16963 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16963
    | (have j0 := eq16963 X0
       grind)
    | exact resolve eq16963 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16963
  have eq16968 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16965 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16965
    | (have j0 := eq16965 X0
       grind)
    | exact resolve eq16965 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16965
  have eq17006 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
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
  have eq17158 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq10
    | (have j1 := eq36 X0 X1
       grind)
    | exact resolve eq10 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq17186 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17006 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq17006
    | (have j0 := eq17006 X0 X1
       grind)
    | exact resolve eq17006 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17006
  have eq17207 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq16968 (τ X0)
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq16968
    | (have j0 := eq16968 (τ X0)
       grind)
    | exact resolve eq16968 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq16968
  have eq18117 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq445 X2 X3 (σ X1) (σ X0)
       have i₂ := eq140 X0 X1
       grind)
    | exact superpose eq140 eq445
    | (have j1 := eq140 X0 X1
       grind)
    | exact resolve eq445 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq445
  have eq85736 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq452 X1 X1
       have i₂ := eq34 (M.op X1 X1) X1 x
       grind)
    | (have i₁ := eq452 X1 X1
       have i₂ := eq34 X0 X1 X1
       grind)
    | exact superpose eq34 eq452
    | (have j1 := eq34 X1 X0 x
       grind)
    | exact resolve eq452 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq90383 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1718
       have i₂ := eq17186 y x
       grind)
    | exact superpose eq17186 eq1718
    | (have j1 := eq17186 (σ y) (σ x)
       grind)
    | (have r₁ := eq1718
       have r₂ := eq17186 y x
       grind)
    | exact resolve eq1718 eq17186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq90384 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq90383
  have eq90395 : x = (k (τ (σ y)) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq84 x
       have i₂ := eq90384
       grind)
    | exact superpose eq90384 eq84
    | exact resolve eq84 eq90384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90581 : x = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq90395
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq90395
    | exact resolve eq90395 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90395
  have eq90670 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq90581
       grind)
    | exact superpose eq90581 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq90581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90673 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq17186 y x
       have i₂ := eq90581
       grind)
    | exact superpose eq90581 eq17186
    | (have j0 := eq17186 y x
       grind)
    | exact resolve eq17186 eq90581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17186 eq90581
  have eq90674 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq90673
  have eq90675 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq90670
  have eq92410 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 X1 y x
       have i₂ := eq90675
       grind)
    | exact superpose eq90675 eq450
    | exact resolve eq450 eq90675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92432 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq992 X0 X1 y x
       have i₂ := eq90675
       grind)
    | exact superpose eq90675 eq992
    | exact resolve eq992 eq90675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90675
  have eq98447 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1751 x x
       have i₂ := eq90384
       grind)
    | exact superpose eq90384 eq1751
    | exact resolve eq1751 eq90384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751
  have eq98714 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq98447
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq98447
    | exact resolve eq98447 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98447
  have eq112079 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92410 (σ x) (σ x)
       have i₂ := eq90384
       grind)
    | exact superpose eq90384 eq92410
    | exact resolve eq92410 eq90384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92410
  have eq112829 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq112079
  have eq132947 : (σ (M.op x y)) ≠ (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq112829
       grind)
    | exact superpose eq112829 eq14
    | exact resolve eq14 eq112829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112829
  have eq136098 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq132947
       have i₂ := eq90674
       grind)
    | exact superpose eq90674 eq132947
    | exact resolve eq132947 eq90674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90674 eq132947
  have eq136099 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq136098
  have eq186494 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq98714
       grind)
    | exact superpose eq98714 eq9
    | exact resolve eq9 eq98714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98714
  have eq186542 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq186494
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq186494
    | exact resolve eq186494 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186494
  have eq189894 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq32 x x
       have i₂ := eq186542
       grind)
    | exact superpose eq186542 eq32
    | exact resolve eq32 eq186542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq186542
  have eq189902 : y = (M.op x x) ∨ x = y := by grind
  clear eq189894
  have eq306176 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X1
       have i₂ := eq131 (σ X1) X0
       grind)
    | exact superpose eq131 eq84
    | (have j1 := eq131 (σ X1) X0
       grind)
    | exact resolve eq84 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq131
  have eq306199 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq306176 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq306176
    | (have j0 := eq306176 X0 X1
       grind)
    | exact resolve eq306176 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306176
  have eq306249 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq306199 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq306199
    | (have j0 := eq306199 X0 X1
       grind)
    | exact resolve eq306199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306199
  have eq324055 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq306249 x x
       have i₂ := eq90384
       grind)
    | exact superpose eq90384 eq306249
    | (have j0 := eq306249 x x
       grind)
    | exact resolve eq306249 eq90384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90384 eq306249
  have eq324126 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq324055
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq324055
    | exact resolve eq324055 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324055
  have eq371886 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq324126
  have eq371906 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq371886
       have r₂ := eq189902
       grind)
    | exact resolve eq371886 eq189902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189902 eq371886
  have eq386520 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1792 x
       have i₂ := eq371906
       grind)
    | exact superpose eq371906 eq1792
    | (have j0 := eq1792 x
       grind)
    | exact resolve eq1792 eq371906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371906
  have eq386543 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq386520
  have eq400050 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92432 (σ x) (σ x)
       have i₂ := eq386543
       grind)
    | exact superpose eq386543 eq92432
    | exact resolve eq92432 eq386543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92432
  have eq400065 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq400050
  have eq496320 : (σ x) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq386543
       have i₂ := eq400065
       grind)
    | exact superpose eq400065 eq386543
    | exact resolve eq386543 eq400065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386543 eq400065
  have eq496503 : (σ x) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq496320
  have eq496512 : y = (M.op x x) := by
    first
    | (have r₁ := eq496503
       have r₂ := eq136099
       grind)
    | exact resolve eq496503 eq136099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136099 eq496503
  have eq500906 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 y) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq269 x X1 x x
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq269
    | exact resolve eq269 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq501019 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 X1 x x
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq450
    | exact resolve eq450 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq501020 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq452 x x
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq452
    | exact resolve eq452 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq501098 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x X2) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq717 X0 X1 x X2 x
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq717
    | exact resolve eq717 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq501129 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq987 X0 X1 X2 x x
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq987
    | exact resolve eq987 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq501131 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq992 X0 X1 x x
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq992
    | exact resolve eq992 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq501206 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) := by
    intro X2
    first
    | (have i₁ := eq501129 x x X2
       have i₂ := eq501131 x x
       grind)
    | exact superpose eq501131 eq501129
    | exact resolve eq501129 eq501131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501129
  have eq501233 : ∀ X1 : G, (M.op x y) = (M.op X1 y) ∨ y = (k x x) := by
    intro X1
    first
    | (have i₁ := eq500906 x X1
       have i₂ := eq501131 x X1
       grind)
    | exact superpose eq501131 eq500906
    | exact resolve eq500906 eq501131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500906 eq501131
  have eq530154 : (τ (M.op x y)) ≠ (τ (M.op x y)) ∨ (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
    first
    | (have i₁ := eq17207 (M.op x y)
       have i₂ := eq501020
       grind)
    | exact superpose eq501020 eq17207
    | (have j0 := eq17207 (M.op x y)
       grind)
    | exact resolve eq17207 eq501020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17207 eq501020
  have eq530169 : (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by grind
  clear eq530154
  have eq551698 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ y = (k x x) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq501233 X1
       have i₂ := eq501233 X0
       grind)
    | (have i₁ := eq501233 X1
       have i₂ := eq501233 x
       grind)
    | exact superpose eq501233 eq501233
    | exact resolve eq501233 eq501233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551734 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 (M.op X0 y)) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq501206 x
       have i₂ := eq501233 X1
       grind)
    | (have i₁ := eq501206 x
       have i₂ := eq501233 x
       grind)
    | exact superpose eq501233 eq501206
    | exact resolve eq501206 eq501233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501233
  have eq552387 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have j0 := eq551698 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551698
  have eq656929 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq501098 (τ (M.op x y)) (τ (M.op x y)) X0
       have i₂ := eq530169
       grind)
    | exact superpose eq530169 eq501098
    | exact resolve eq501098 eq530169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501098
  have eq656948 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (τ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq656929 X0
       have i₂ := eq530169
       grind)
    | exact superpose eq530169 eq656929
    | exact resolve eq656929 eq530169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530169 eq656929
  have eq657087 : (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq656948 x
       have i₂ := eq501206 (M.op x x)
       grind)
    | exact superpose eq501206 eq656948
    | exact resolve eq656948 eq501206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501206 eq656948
  have eq658166 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq657087
       grind)
    | exact superpose eq657087 eq10
    | exact resolve eq10 eq657087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657087
  have eq659084 : ∀ X0 : G, (M.op X0 y) = (σ (M.op X0 y)) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq658166
       have i₂ := eq552387 x x
       grind)
    | (have i₁ := eq658166
       have i₂ := eq552387 X0 x
       grind)
    | exact superpose eq552387 eq658166
    | exact resolve eq658166 eq552387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665821 : ∀ X0 : G, (k X0 (σ (τ X0))) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq17158 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17158
  have eq665822 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq665821 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq665821
    | (have j0 := eq665821 X0
       grind)
    | exact resolve eq665821 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665821
  have eq665897 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq665822 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq665822
    | (have j0 := eq665822 (σ X0)
       grind)
    | exact resolve eq665822 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665822
  have eq665912 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq665897 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq665897
    | (have j0 := eq665897 X0
       grind)
    | exact resolve eq665897 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665897
  have eq786922 : y = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq85736 x x
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq85736
    | exact resolve eq85736 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85736
  have eq786970 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq665912 y
       have i₂ := eq786922
       grind)
    | exact superpose eq786922 eq665912
    | (have j0 := eq665912 y
       grind)
    | exact resolve eq665912 eq786922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665912 eq786922
  have eq786982 : (σ y) = (σ (M.op y y)) ∨ y = (k x x) := by grind
  clear eq786970
  have eq787171 : ∀ X0 : G, (σ y) = (σ (M.op X0 y)) ∨ y = (k x x) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq786982
       have i₂ := eq552387 y X0
       grind)
    | (have i₁ := eq786982
       have i₂ := eq552387 X0 y
       grind)
    | exact superpose eq552387 eq786982
    | exact resolve eq786982 eq552387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552387 eq786982
  have eq787210 : ∀ X0 : G, (σ y) = (σ (M.op X0 y)) ∨ y = (k x x) := by
    intro X0
    first
    | (have j0 := eq787171 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787171
  have eq787568 : ∀ X0 : G, (σ y) = (M.op X0 y) ∨ y = (k x x) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq659084 X0
       have i₂ := eq787210 X0
       grind)
    | exact superpose eq787210 eq659084
    | exact resolve eq659084 eq787210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659084
  have eq787600 : ∀ X0 : G, (σ y) = (M.op X0 y) ∨ y = (k x x) := by
    intro X0
    first
    | (have j0 := eq787568 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787568
  have eq795801 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) ∨ y = (k x x) ∨ y = (k x x) := by
    intro X1
    first
    | (have i₁ := eq551734 x X1
       have i₂ := eq787600 x
       grind)
    | exact superpose eq787600 eq551734
    | exact resolve eq551734 eq787600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551734 eq787600
  have eq796246 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) ∨ y = (k x x) := by
    intro X1
    first
    | (have j0 := eq795801 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795801
  have eq802147 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq796246 (σ x)
       grind)
    | exact superpose eq796246 eq14
    | exact resolve eq14 eq796246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796246
  have eq802160 : y = (k x x) := by
    first
    | (have r₁ := eq802147
       have r₂ := eq787210 x
       grind)
    | exact resolve eq802147 eq787210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787210 eq802147
  have eq804705 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1792 x
       have i₂ := eq802160
       grind)
    | exact superpose eq802160 eq1792
    | (have j0 := eq1792 x
       grind)
    | exact resolve eq1792 eq802160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq974653 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq18117 x x x x
       have i₂ := eq802160
       grind)
    | exact superpose eq802160 eq18117
    | exact resolve eq18117 eq802160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18117 eq802160
  have eq974764 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq974653 x x
       have i₂ := eq501019 x x
       grind)
    | exact superpose eq501019 eq974653
    | exact resolve eq974653 eq501019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501019 eq974653
  have eq974783 : (M.op x y) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq974764
       grind)
    | exact superpose eq974764 eq14
    | exact resolve eq14 eq974764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974764
  have eq974973 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq974783
       have r₂ := eq658166
       grind)
    | exact resolve eq974783 eq658166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974783
  have eq975172 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq974973
       grind)
    | exact superpose eq974973 eq14
    | exact resolve eq14 eq974973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq975193 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq804705
       have i₂ := eq974973
       grind)
    | exact superpose eq974973 eq804705
    | (have r₁ := eq804705
       have r₂ := eq974973
       grind)
    | exact resolve eq804705 eq974973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804705
  have eq975194 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq974973
       grind)
    | exact superpose eq974973 eq9
    | exact resolve eq9 eq974973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974973
  have eq975250 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq975193
  have eq975274 : x = y := by
    first
    | (have i₁ := eq975194
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq975194
    | exact resolve eq975194 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975194
  have eq975275 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq975172
       have i₂ := eq975250
       grind)
    | exact superpose eq975250 eq975172
    | exact resolve eq975172 eq975250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975172 eq975250
  have eq975277 : (M.op x y) ≠ (σ x) := by
    first
    | (have i₁ := eq975275
       have i₂ := eq658166
       grind)
    | exact superpose eq658166 eq975275
    | exact resolve eq975275 eq658166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975275
  have eq975279 : (σ x) ≠ (M.op x x) := by
    first
    | (have i₁ := eq975277
       have i₂ := eq975274
       grind)
    | exact superpose eq975274 eq975277
    | exact resolve eq975277 eq975274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975277
  have eq975281 : y ≠ (σ x) := by
    first
    | (have i₁ := eq975279
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq975279
    | exact resolve eq975279 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975279
  have eq975283 : x ≠ (σ x) := by
    first
    | (have i₁ := eq975281
       have i₂ := eq975274
       grind)
    | exact superpose eq975274 eq975281
    | exact resolve eq975281 eq975274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975281
  have eq975603 : (M.op x x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq658166
       have i₂ := eq975274
       grind)
    | exact superpose eq975274 eq658166
    | exact resolve eq658166 eq975274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658166
  have eq975723 : y = (σ y) := by
    first
    | (have i₁ := eq975603
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq975603
    | exact resolve eq975603 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496512 eq975603
  have eq975783 : x = (σ x) := by
    first
    | (have i₁ := eq975723
       have i₂ := eq975274
       grind)
    | exact superpose eq975274 eq975723
    | exact resolve eq975723 eq975274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975274 eq975723
  have eq975825 : False := by grind
  exact eq975825

/-- `Equation4315`: `x ◇ (y ◇ x) = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation4315 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4315 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4315.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X1 X2)) := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq8 X2 X1 X2
       have i₂ := eq8 X2 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq30 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
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
  have eq76 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq27
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq152 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (M.op X1 X3) = (k X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq91 X0 (M.op X1 X3)
       have i₂ := eq20 X0 X1 X3 X2
       grind)
    | (have i₁ := eq91 X0 (M.op X1 X3)
       have i₂ := eq20 X0 X1 X2 X3
       grind)
    | exact superpose eq20 eq91
    | (have j0 := eq91 X0 (M.op X1 X3)
       grind)
    | (have r₁ := eq91 X0 (M.op X0 (M.op X0 X3))
       have r₂ := eq20 X0 X0 (M.op X0 X3) X3
       grind)
    | (have r₁ := eq91 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq20 X0 X0 X2 (M.op X0 X2)
       grind)
    | exact resolve eq91 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq305 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq311 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ (k X0 X1))) = (M.op X2 (M.op (σ X0) X3)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 (σ X0) X3 (σ X1)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq20
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq20 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq319 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq33 X0 X2
       grind)
    | exact superpose eq33 eq13
    | (have j1 := eq33 X0 X2
       grind)
    | exact resolve eq13 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq560 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
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
  have eq617 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq560 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq560
    | (have j0 := eq560 X0 X1
       grind)
    | exact resolve eq560 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq1330 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq305
       have i₂ := eq617 y x
       grind)
    | exact superpose eq617 eq305
    | (have j1 := eq617 (σ y) (σ x)
       grind)
    | (have r₁ := eq305
       have r₂ := eq617 y x
       grind)
    | exact resolve eq305 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq1331 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1330
  have eq1374 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (σ (k X1 X2)) = (M.op (σ X1) (σ X2)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq317 X1 X2
       have i₂ := eq317 X1 X0
       grind)
    | (have i₁ := eq317 X0 X1
       have i₂ := eq317 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq317 eq317
    | (have j0 := eq317 X1 X2
       have j1 := eq317 X1 X2
       grind)
    | exact resolve eq317 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1381 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq317 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq317
    | exact resolve eq317 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1419 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ (k X0 X1))) = (M.op X2 (M.op (σ X0) X3)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 (σ X0) X3 (σ X1)
       have i₂ := eq317 X0 X1
       grind)
    | exact superpose eq317 eq20
    | (have j1 := eq317 X0 X1
       grind)
    | exact resolve eq20 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq1431 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1381 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq1381
    | (have j0 := eq1381 X0 X1
       grind)
    | exact resolve eq1381 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq1381
  have eq3587 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (σ (τ X0)) X3)) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq311 (τ X0) (τ X1) X2 X3
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq311
    | (have j0 := eq311 (τ X0) (τ X1) X2 X3
       grind)
    | exact resolve eq311 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq3916 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (σ (τ X0)) X3)) = (M.op X2 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3587 X0 X1 X2 X3
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3587
    | (have j0 := eq3587 X0 X1 X2 X3
       grind)
    | exact resolve eq3587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587
  have eq3918 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op X2 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3916 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3916
    | (have j0 := eq3916 X0 X1 X2 X3
       grind)
    | exact resolve eq3916 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3916
  have eq3919 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X2 (M.op X0 X3)) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3918 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3918
    | (have j0 := eq3918 X0 X1 X2 X3
       grind)
    | exact resolve eq3918 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3918
  have eq3920 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = X1 ∨ (M.op X2 (M.op X0 X3)) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3919 X0 X1 X2 X3
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3919
    | (have j0 := eq3919 X0 X1 X2 X3
       grind)
    | exact resolve eq3919 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3919
  have eq5595 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1431 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1431
    | (have j0 := eq1431 X1 (τ X0)
       grind)
    | exact resolve eq1431 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431
  have eq10596 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  clear eq319
  have eq32561 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq152 X0 X0 x (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq49968 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10596 (τ X1) (τ X0)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq10596
    | exact resolve eq10596 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq49990 : (σ y) = (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10596 x x
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq10596
    | exact resolve eq10596 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331
  have eq50029 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq10596 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10596
  have eq50030 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq50029 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50029
  have eq50035 : (σ y) = (σ (k x x)) ∨ y = (M.op x x) := by grind
  clear eq49990
  have eq50067 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (k (τ X0) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq49968 X0 X1
       have i₂ := eq50030 (τ X0)
       grind)
    | exact superpose eq50030 eq49968
    | (have j0 := eq49968 X0 X1
       grind)
    | exact resolve eq49968 eq50030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49968
  have eq50084 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50067 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq50067
    | (have j0 := eq50067 X0 X1
       grind)
    | exact resolve eq50067 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50067
  have eq50091 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50084 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50084
    | (have j0 := eq50084 X0 X1
       grind)
    | exact resolve eq50084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50084
  have eq50094 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50091 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq50091
    | (have j0 := eq50091 X0 X1
       grind)
    | exact resolve eq50091 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50091
  have eq50096 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50094 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq50094
    | (have j0 := eq50094 X0 X1
       grind)
    | exact resolve eq50094 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50094
  have eq50097 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50096 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50096
    | (have j0 := eq50096 X0 X1
       grind)
    | exact resolve eq50096 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50096
  have eq50098 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50097 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq50097
    | (have j0 := eq50097 X0 X1
       grind)
    | exact resolve eq50097 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50097
  have eq50123 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50030 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50030
    | exact resolve eq50030 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50217 : ∀ X0 X1 : G, (τ X1) = (τ (σ (k X0 X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5595 X1 (σ X0)
       have i₂ := eq50030 X0
       grind)
    | exact superpose eq50030 eq5595
    | (have j0 := eq5595 X1 (σ X0)
       grind)
    | exact resolve eq5595 eq50030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5595
  have eq50230 : ∀ X0 X1 X2 : G, (M.op X1 (σ (k X0 X0))) = (M.op X1 (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X1 (σ X0) X2 (σ X0)
       have i₂ := eq50030 X0
       grind)
    | exact superpose eq50030 eq20
    | exact resolve eq20 eq50030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50280 : ∀ X0 X1 : G, (τ X1) = (k X0 X0) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50217 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq50217
    | (have j0 := eq50217 X0 X1
       grind)
    | exact resolve eq50217 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50217
  have eq50310 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq50123 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq50123
    | exact resolve eq50123 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq50123
  have eq50323 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq50310 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50310
    | exact resolve eq50310 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50310
  have eq51544 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq50035
       grind)
    | exact superpose eq50035 eq9
    | exact resolve eq9 eq50035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50035
  have eq51636 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq51544
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq51544
    | exact resolve eq51544 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51544
  have eq51672 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq51636
       have i₂ := eq50323 x
       grind)
    | exact superpose eq50323 eq51636
    | exact resolve eq51636 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51636
  have eq51673 : y = (M.op x x) := by grind
  clear eq51672
  have eq51711 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 x X1 x
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq20
    | exact resolve eq20 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq51755 : (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq32561 x x
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq32561
    | exact resolve eq32561 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51998 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X0 (k x X2)) ∨ (M.op x x) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq3920 x X2 X0 x
       have i₂ := eq51711 X0 x
       grind)
    | exact superpose eq51711 eq3920
    | (have j0 := eq3920 x X2 X2 x
       grind)
    | exact resolve eq3920 eq51711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3920 eq51711
  have eq52123 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X0 (k x X2)) ∨ y = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq51998 X0 X2
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq51998
    | (have j0 := eq51998 X0 X2
       grind)
    | exact resolve eq51998 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51998
  have eq53161 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) X2)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50230 X0 X1 X2
       have i₂ := eq50323 X0
       grind)
    | exact superpose eq50323 eq50230
    | exact resolve eq50230 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50230
  have eq53894 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53161 x X0 X1
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq53161
    | exact resolve eq53161 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53161
  have eq54334 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq32561 (σ x) x
       have i₂ := eq53894 (σ x) x
       grind)
    | exact superpose eq53894 eq32561
    | exact resolve eq32561 eq53894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32561
  have eq55014 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq1419 x (M.op x y) X0 X1
       have i₂ := eq51755
       grind)
    | exact superpose eq51755 eq1419
    | (have j0 := eq1419 x (M.op x y) x x
       grind)
    | exact resolve eq1419 eq51755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419
  have eq55116 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq55014 X0 x
       have i₂ := eq53894 X0 x
       grind)
    | exact superpose eq53894 eq55014
    | exact resolve eq55014 eq53894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53894 eq55014
  have eq55128 : ∀ X0 : G, (M.op x y) = (τ (σ (k x x))) ∨ (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq55116 X0
       have i₂ := eq50030 x
       grind)
    | exact superpose eq50030 eq55116
    | (have j0 := eq55116 X0
       grind)
    | exact resolve eq55116 eq50030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50030 eq55116
  have eq55138 : ∀ X0 : G, (M.op x y) = (k x x) ∨ (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq55128 X0
       have i₂ := eq9 (k x x)
       grind)
    | exact superpose eq9 eq55128
    | (have j0 := eq55128 X0
       grind)
    | exact resolve eq55128 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55128
  have eq55144 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq55138 X0
       have i₂ := eq50323 x
       grind)
    | exact superpose eq50323 eq55138
    | (have j0 := eq55138 X0
       grind)
    | exact resolve eq55138 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55138
  have eq55146 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq55144 X0
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq55144
    | (have j0 := eq55144 X0
       grind)
    | exact resolve eq55144 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55144
  have eq55901 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50098 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50098
  have eq55904 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55901 X0 X1
       have i₂ := eq50323 X0
       grind)
    | exact superpose eq50323 eq55901
    | (have j0 := eq55901 X0 X1
       grind)
    | (have r₁ := eq55901 X0 X0
       have r₂ := eq50323 X0
       grind)
    | exact resolve eq55901 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55901
  have eq55993 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55904 X0 X1
       have i₂ := eq50323 X0
       grind)
    | exact superpose eq50323 eq55904
    | (have j0 := eq55904 X0 X1
       grind)
    | exact resolve eq55904 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55904
  have eq56345 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq55993 x x
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq55993
    | exact resolve eq55993 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51673 eq55993
  have eq56564 : ∀ X0 : G, y ≠ (M.op x y) ∨ y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq56345 (k x X0)
       have i₂ := eq52123 x X0
       grind)
    | exact superpose eq52123 eq56345
    | (have j0 := eq56345 y
       have j1 := eq52123 X0 (k x (k x X0))
       grind)
    | (have r₁ := eq56345 X0
       have r₂ := eq52123 X0 (M.op x X0)
       grind)
    | exact resolve eq56345 eq52123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52123 eq56345
  have eq58613 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq41 x (M.op (σ x) (σ y))
       have i₂ := eq54334
       grind)
    | exact superpose eq54334 eq41
    | exact resolve eq41 eq54334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq54334
  have eq60805 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq50280 X0 (σ X1)
       grind)
    | exact superpose eq50280 eq9
    | (have j1 := eq50280 X0 (σ X1)
       grind)
    | exact resolve eq9 eq50280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50280
  have eq60908 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60805 X0 X1
       have i₂ := eq50323 X0
       grind)
    | exact superpose eq50323 eq60805
    | (have j0 := eq60805 X0 X1
       grind)
    | exact resolve eq60805 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50323 eq60805
  have eq60950 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60908 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq60908
    | (have j0 := eq60908 X0 X1
       grind)
    | exact resolve eq60908 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60908
  have eq62499 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (σ (k X1 X2)) = (σ (M.op X1 X2)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq617 X2 X1
       have i₂ := eq60950 X1 X0
       grind)
    | (have i₁ := eq617 X0 X1
       have i₂ := eq60950 X0 (M.op X1 X1)
       grind)
    | exact superpose eq60950 eq617
    | (have j0 := eq617 X2 X1
       have j1 := eq60950 X1 X0
       grind)
    | exact resolve eq617 eq60950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617 eq60950
  have eq62854 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = X0 ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq1374 y x X0
       grind)
    | exact superpose eq1374 eq14
    | (have j1 := eq1374 y x X0
       grind)
    | (have r₁ := eq14
       have r₂ := eq1374 (σ (M.op x y)) x (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq1374 (M.op (σ x) (σ y)) x (σ (M.op x y))
       grind)
    | exact resolve eq14 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq62858 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq62854 X0
       have j1 := eq62499 (σ (k x X0)) x (M.op (σ x) (σ X0))
       grind)
    | (have r₁ := eq62854 X0
       have r₂ := eq62499 (σ (M.op x y)) x (σ (k x y))
       grind)
    | (have r₁ := eq62854 X0
       have r₂ := eq62499 (σ (k x y)) x (σ (M.op x y))
       grind)
    | (have r₁ := eq62854 X0
       have r₂ := eq62499 X0 x y
       grind)
    | exact resolve eq62854 eq62499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62499 eq62854
  have eq72325 : (M.op (σ x) (σ y)) = (σ (k x (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq62858 (M.op x y)
       have i₂ := eq55146 (σ x)
       grind)
    | exact superpose eq55146 eq62858
    | (have j0 := eq62858 (M.op x y)
       grind)
    | exact resolve eq62858 eq55146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55146 eq62858
  have eq72361 : (M.op (σ x) (σ y)) = (σ (k x (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq72325
  have eq72365 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq72361
       have i₂ := eq51755
       grind)
    | exact superpose eq51755 eq72361
    | exact resolve eq72361 eq51755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51755 eq72361
  have eq72370 : y = (M.op x y) := by
    first
    | (have r₁ := eq72365
       have r₂ := eq14
       grind)
    | exact resolve eq72365 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72365
  have eq72389 : ∀ X0 : G, y ≠ y ∨ y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq56564 X0
       have i₂ := eq72370
       grind)
    | exact superpose eq72370 eq56564
    | (have j0 := eq56564 X0
       grind)
    | (have r₁ := eq56564 X0
       have r₂ := eq72370
       grind)
    | exact resolve eq56564 eq72370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56564
  have eq72505 : ∀ X0 : G, y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq72389 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72389
  have eq73386 : y = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq72505 (τ (M.op (σ x) (σ y)))
       have i₂ := eq58613
       grind)
    | exact superpose eq58613 eq72505
    | (have j0 := eq72505 (k x (τ (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq72505 eq58613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72505
  have eq73658 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq73386
       have i₂ := eq58613
       grind)
    | exact superpose eq58613 eq73386
    | exact resolve eq73386 eq58613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58613 eq73386
  have eq73659 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq73658
  have eq73822 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq73659
       grind)
    | exact superpose eq73659 eq10
    | exact resolve eq10 eq73659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73659
  have eq74390 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq73822
       grind)
    | exact superpose eq73822 eq14
    | exact resolve eq14 eq73822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73822
  have eq74601 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq74390
       have i₂ := eq72370
       grind)
    | exact superpose eq72370 eq74390
    | exact resolve eq74390 eq72370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72370 eq74390
  have eq74602 : False := by grind
  exact eq74602
