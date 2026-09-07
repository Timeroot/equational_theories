import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation635`: `x = x ◇ (y ◇ ((x ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation635 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law635 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law635.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X0 X2) X0))) = X0 := by
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
  have eq18 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op x (M.op (M.op X0 x) X0))
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op X0 X0) X0 x
       have i₂ := eq18 X0 (M.op (M.op X0 X0) x)
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq22 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq22
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq42 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq43 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38
    | exact resolve eq38 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq45 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq50 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
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
  clear eq27
  have eq61 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42
    | exact resolve eq42 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq82 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
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
  have eq117 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq119 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq50
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq50 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq131 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq117
    | exact resolve eq117 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq201 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq22
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq22 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq131
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq131 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq131
  have eq283 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq262 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq262
    | (have j0 := eq262 X0 X1
       grind)
    | exact resolve eq262 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq704 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq45
    | exact resolve eq45 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq10
    | (have j1 := eq45 X1 X0
       grind)
    | exact resolve eq10 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq787 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq704 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq704
    | (have j0 := eq704 X0 X1
       grind)
    | exact resolve eq704 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq846 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq848 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq787 X0 X1
       grind)
    | (have i₁ := eq22 X0
       have i₂ := eq787 (M.op X0 X0) X1
       grind)
    | exact superpose eq787 eq22
    | (have j1 := eq787 X0 X1
       grind)
    | exact resolve eq22 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1282 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (σ (k X0 X0)))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X0) X1
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq18
    | (have j1 := eq53 X0 X0
       grind)
    | exact resolve eq18 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1283 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0)
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq22
    | (have j1 := eq53 X0 X0
       grind)
    | exact resolve eq22 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq53
  have eq2668 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq82
    | (have j0 := eq82 X1 (σ X0)
       grind)
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq2743 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2668 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2668
    | (have j0 := eq2668 X0 X1
       grind)
    | exact resolve eq2668 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2668
  have eq8837 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq283 x y
       grind)
    | exact superpose eq283 eq14
    | (have j1 := eq283 x y
       grind)
    | exact resolve eq14 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq8866 : y = (k y x) := by
    first
    | (have j1 := eq846 x y
       grind)
    | (have r₁ := eq8837
       have r₂ := eq846 x y
       grind)
    | exact resolve eq8837 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846 eq8837
  have eq9287 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32 x y
       have i₂ := eq8866
       grind)
    | exact superpose eq8866 eq32
    | (have j0 := eq32 x y
       grind)
    | exact resolve eq32 eq8866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq9290 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq787 x y
       have i₂ := eq8866
       grind)
    | exact superpose eq8866 eq787
    | (have j0 := eq787 x y
       grind)
    | exact resolve eq787 eq8866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq9291 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq848 x y
       have i₂ := eq8866
       grind)
    | exact superpose eq8866 eq848
    | (have j0 := eq848 x y
       grind)
    | exact resolve eq848 eq8866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq10544 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq9287
  have eq14662 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq736 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq14663 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14662 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14662
    | (have j0 := eq14662 X0
       grind)
    | exact resolve eq14662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14662
  have eq14749 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq14663 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq14663
    | (have j0 := eq14663 (σ X0)
       grind)
    | exact resolve eq14663 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14663
  have eq14761 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14749 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq14749
    | (have j0 := eq14749 X0
       grind)
    | exact resolve eq14749 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14749
  have eq15815 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq14761 X0
       have i₂ := eq2743 X0 X0
       grind)
    | exact superpose eq2743 eq14761
    | (have j0 := eq14761 X0
       have j1 := eq2743 X0 X0
       grind)
    | (have r₁ := eq14761 x
       have r₂ := eq2743 x x
       grind)
    | exact resolve eq14761 eq2743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2743 eq14761
  have eq15832 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq15815 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15815
  have eq15980 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq201 x y
       grind)
    | exact superpose eq201 eq14
    | (have j1 := eq201 x y
       grind)
    | exact resolve eq14 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16017 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq16030 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15980
       have i₂ := eq8866
       grind)
    | exact superpose eq8866 eq15980
    | exact resolve eq15980 eq8866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15980
  have eq18669 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op X1 (k (σ (τ X0)) X0))) ∨ (σ (τ X0)) = (k (σ (τ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1282 (τ X0) X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1282
    | exact resolve eq1282 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1282
  have eq18760 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 X0))) = X0 ∨ (σ (τ X0)) = (k (σ (τ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18669 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18669
    | (have j0 := eq18669 X0 X1
       grind)
    | exact resolve eq18669 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18669
  have eq18771 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18760 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18760
    | (have j0 := eq18760 X0 X1
       grind)
    | exact resolve eq18760 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18760
  have eq18829 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 (k X0 X0) X0 x
       have i₂ := eq18771 X0 (M.op (k X0 X0) x)
       grind)
    | exact superpose eq18771 eq8
    | (have j1 := eq18771 X0 x
       grind)
    | exact resolve eq8 eq18771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18771
  have eq24232 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16017 (τ X1) (τ X0)
       have i₂ := eq61 X1 X0
       grind)
    | exact superpose eq61 eq16017
    | (have j0 := eq16017 (τ X1) (τ X0)
       grind)
    | exact resolve eq16017 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq24238 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16017 x y
       have i₂ := eq8866
       grind)
    | exact superpose eq8866 eq16017
    | (have j0 := eq16017 x y
       grind)
    | exact resolve eq16017 eq8866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8866 eq16017
  have eq24292 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24232 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq24232
    | (have j0 := eq24232 X0 X1
       grind)
    | exact resolve eq24232 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24232
  have eq24306 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24292 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq24292
    | (have j0 := eq24292 X0 X1
       grind)
    | exact resolve eq24292 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24292
  have eq24313 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24306 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24306
    | (have j0 := eq24306 X0 X1
       grind)
    | exact resolve eq24306 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24306
  have eq24314 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24313 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24313
    | (have j0 := eq24313 X0 X1
       grind)
    | exact resolve eq24313 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24313
  have eq27926 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16030
       have i₂ := eq9291
       grind)
    | exact superpose eq9291 eq16030
    | (have r₁ := eq16030
       have r₂ := eq9291
       grind)
    | exact resolve eq16030 eq9291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27927 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16030
       have i₂ := eq9290
       grind)
    | exact superpose eq9290 eq16030
    | (have r₁ := eq16030
       have r₂ := eq9290
       grind)
    | exact resolve eq16030 eq9290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9290 eq16030
  have eq27931 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq27927
  have eq27932 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27926
  have eq28460 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq27931
       grind)
    | exact superpose eq27931 eq14
    | exact resolve eq14 eq27931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27931
  have eq30516 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq27932
       grind)
    | exact superpose eq27932 eq14
    | exact resolve eq14 eq27932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30528 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119 (σ x) y
       have i₂ := eq27932
       grind)
    | exact superpose eq27932 eq119
    | (have j0 := eq119 (σ x) y
       grind)
    | exact resolve eq119 eq27932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27932
  have eq30555 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30528
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq30528
    | exact resolve eq30528 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30528
  have eq30578 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq24314 y x
       grind)
    | (have r₁ := eq30555
       have r₂ := eq24314 y x
       grind)
    | exact resolve eq30555 eq24314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24314 eq30555
  have eq31265 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30516
       have i₂ := eq9291
       grind)
    | exact superpose eq9291 eq30516
    | exact resolve eq30516 eq9291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9291 eq30516
  have eq31270 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq31265
  have eq31514 : (τ (σ x)) = (k y (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119 (σ y) y
       have i₂ := eq30578
       grind)
    | exact superpose eq30578 eq119
    | exact resolve eq119 eq30578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq30578
  have eq31566 : (τ (σ x)) = (k y (τ (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq31514
       have r₂ := eq31270
       grind)
    | exact resolve eq31514 eq31270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31270 eq31514
  have eq31584 : (k y y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31566
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq31566
    | exact resolve eq31566 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31566
  have eq31589 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31584
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq31584
    | exact resolve eq31584 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31584
  have eq31791 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18829 y
       have i₂ := eq31589
       grind)
    | exact superpose eq31589 eq18829
    | exact resolve eq18829 eq31589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18829 eq31589
  have eq31814 : x = (M.op x y) ∨ x = y := by grind
  clear eq31791
  have eq31821 : x = (M.op x y) := by
    first
    | (have r₁ := eq31814
       have r₂ := eq10544
       grind)
    | exact resolve eq31814 eq10544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10544 eq31814
  have eq32041 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq28460
       have i₂ := eq31821
       grind)
    | exact superpose eq31821 eq28460
    | exact resolve eq28460 eq31821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28460
  have eq32059 : x = (M.op y y) := by grind
  clear eq32041
  have eq32299 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15832 y
       have i₂ := eq32059
       grind)
    | exact superpose eq32059 eq15832
    | exact resolve eq15832 eq32059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15832 eq32059
  have eq35415 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1283 y
       have i₂ := eq32299
       grind)
    | exact superpose eq32299 eq1283
    | exact resolve eq1283 eq32299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283 eq32299
  have eq35454 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq35415
  have eq35459 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq35454
       have r₂ := eq24238
       grind)
    | exact resolve eq35454 eq24238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24238 eq35454
  have eq36049 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35459
       grind)
    | exact superpose eq35459 eq14
    | exact resolve eq14 eq35459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35459
  have eq36105 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq36049
       have i₂ := eq31821
       grind)
    | exact superpose eq31821 eq36049
    | exact resolve eq36049 eq31821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31821 eq36049
  have eq36106 : False := by grind
  exact eq36106

/-- `Equation635`: `x = x ◇ (y ◇ ((x ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation635 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law635 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law635.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X0 X2) X0))) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq18 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op x (M.op (M.op X0 x) X0))
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op X0 X0) X0 x
       have i₂ := eq18 X0 (M.op (M.op X0 X0) x)
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq22 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq22
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq41 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq43 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq52 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq43
    | exact resolve eq43 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq61 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq64 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq67 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq41
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq72 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq115 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1
       have i₂ := eq12 X0 (τ X1)
       grind)
    | (have i₁ := eq52 X0
       have i₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq12 eq52
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq201 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq22
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq22 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq72
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq72 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq72
  have eq283 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq262 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq262
    | (have j0 := eq262 X0 X1
       grind)
    | exact resolve eq262 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq722 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
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
  have eq754 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
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
  clear eq38
  have eq805 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq722 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq722
    | (have j0 := eq722 X0 X1
       grind)
    | exact resolve eq722 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq864 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq866 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq805 X0 X1
       grind)
    | (have i₁ := eq22 X0
       have i₂ := eq805 (M.op X0 X0) X1
       grind)
    | exact superpose eq805 eq22
    | (have j1 := eq805 X0 X1
       grind)
    | exact resolve eq22 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1312 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (σ (k X0 X0)))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X0) X1
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq18
    | (have j1 := eq53 X0 X0
       grind)
    | exact resolve eq18 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1313 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22 (σ x)
       have i₂ := eq53 x x
       grind)
    | exact superpose eq53 eq22
    | (have j1 := eq53 X0 X0
       grind)
    | exact resolve eq22 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq53
  have eq7513 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq283 x y
       grind)
    | exact superpose eq283 eq14
    | (have j1 := eq283 x y
       grind)
    | exact resolve eq14 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq7540 : y = (k x y) := by
    first
    | (have j1 := eq864 x y
       grind)
    | (have r₁ := eq7513
       have r₂ := eq864 x y
       grind)
    | exact resolve eq7513 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864 eq7513
  have eq8121 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32 x y
       have i₂ := eq7540
       grind)
    | exact superpose eq7540 eq32
    | (have j0 := eq32 x y
       grind)
    | exact resolve eq32 eq7540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq8123 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq805 x y
       have i₂ := eq7540
       grind)
    | exact superpose eq7540 eq805
    | (have j0 := eq805 x y
       grind)
    | exact resolve eq805 eq7540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq8124 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq866 x y
       have i₂ := eq7540
       grind)
    | exact superpose eq7540 eq866
    | (have j0 := eq866 x y
       grind)
    | exact resolve eq866 eq7540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq9118 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq8121
  have eq14504 : ∀ X0 : G, (k X0 (σ (τ X0))) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq754 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq14505 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14504 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14504
    | (have j0 := eq14504 X0
       grind)
    | exact resolve eq14504 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14504
  have eq14592 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq14505 (σ X0)
       have i₂ := eq115 X0 (σ X0)
       grind)
    | exact superpose eq115 eq14505
    | (have j0 := eq14505 (σ X0)
       have j1 := eq115 X0 (σ X0)
       grind)
    | (have r₁ := eq14505 (σ X0)
       have r₂ := eq115 X0 (σ X0)
       grind)
    | exact resolve eq14505 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq14505
  have eq14596 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq14592 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14592
  have eq14598 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq14596 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq14596
    | (have j0 := eq14596 X0
       grind)
    | exact resolve eq14596 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14596
  have eq14604 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq14598 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq14598
    | (have j0 := eq14598 X0
       grind)
    | exact resolve eq14598 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14598
  have eq15827 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq201 x y
       grind)
    | exact superpose eq201 eq14
    | (have j1 := eq201 x y
       grind)
    | exact resolve eq14 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15863 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq15875 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15827
       have i₂ := eq7540
       grind)
    | exact superpose eq7540 eq15827
    | exact resolve eq15827 eq7540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15827
  have eq18704 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op X1 (k (σ (τ X0)) X0))) ∨ (σ (τ X0)) = (k (σ (τ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1312 (τ X0) X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1312
    | exact resolve eq1312 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1312
  have eq18795 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 X0))) = X0 ∨ (σ (τ X0)) = (k (σ (τ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18704 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18704
    | (have j0 := eq18704 X0 X1
       grind)
    | exact resolve eq18704 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18704
  have eq18804 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18795 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18795
    | (have j0 := eq18795 X0 X1
       grind)
    | exact resolve eq18795 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18795
  have eq18858 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 (k X0 X0) X0 x
       have i₂ := eq18804 X0 (M.op (k X0 X0) x)
       grind)
    | exact superpose eq18804 eq8
    | (have j1 := eq18804 X0 x
       grind)
    | exact resolve eq8 eq18804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18804
  have eq22519 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15863 (τ X0) (τ X1)
       have i₂ := eq61 X1 X0
       grind)
    | exact superpose eq61 eq15863
    | (have j0 := eq15863 (τ X0) (τ X1)
       grind)
    | exact resolve eq15863 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq22534 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15863 x y
       have i₂ := eq7540
       grind)
    | exact superpose eq7540 eq15863
    | (have j0 := eq15863 x y
       grind)
    | exact resolve eq15863 eq7540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7540 eq15863
  have eq22589 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22519 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq22519
    | (have j0 := eq22519 X0 X1
       grind)
    | exact resolve eq22519 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22519
  have eq22600 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22589 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22589
    | (have j0 := eq22589 X0 X1
       grind)
    | exact resolve eq22589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22589
  have eq22602 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22600 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq22600
    | (have j0 := eq22600 X0 X1
       grind)
    | exact resolve eq22600 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22600
  have eq22603 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22602 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22602
    | (have j0 := eq22602 X0 X1
       grind)
    | exact resolve eq22602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22602
  have eq25513 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15875
       have i₂ := eq8124
       grind)
    | exact superpose eq8124 eq15875
    | (have r₁ := eq15875
       have r₂ := eq8124
       grind)
    | exact resolve eq15875 eq8124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25514 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15875
       have i₂ := eq8123
       grind)
    | exact superpose eq8123 eq15875
    | (have r₁ := eq15875
       have r₂ := eq8123
       grind)
    | exact resolve eq15875 eq8123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8123 eq15875
  have eq25518 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq25514
  have eq25519 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq25513
  have eq26116 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq25518
       grind)
    | exact superpose eq25518 eq14
    | exact resolve eq14 eq25518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25518
  have eq28155 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq25519
       grind)
    | exact superpose eq25519 eq14
    | exact resolve eq14 eq25519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28168 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67 (σ x) y
       have i₂ := eq25519
       grind)
    | exact superpose eq25519 eq67
    | (have j0 := eq67 (σ x) y
       grind)
    | exact resolve eq67 eq25519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25519
  have eq28195 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28168
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq28168
    | exact resolve eq28168 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28168
  have eq28218 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq22603 x y
       grind)
    | (have r₁ := eq28195
       have r₂ := eq22603 x y
       grind)
    | exact resolve eq28195 eq22603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22603 eq28195
  have eq28920 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28155
       have i₂ := eq8124
       grind)
    | exact superpose eq8124 eq28155
    | exact resolve eq28155 eq8124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8124 eq28155
  have eq28925 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq28920
  have eq30365 : (τ (σ x)) = (k (τ (σ y)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67 (σ y) y
       have i₂ := eq28218
       grind)
    | exact superpose eq28218 eq67
    | exact resolve eq67 eq28218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq28218
  have eq30409 : (τ (σ x)) = (k (τ (σ y)) y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30365
       have r₂ := eq28925
       grind)
    | exact resolve eq30365 eq28925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28925 eq30365
  have eq30426 : (k y y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30409
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq30409
    | exact resolve eq30409 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30409
  have eq30431 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30426
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq30426
    | exact resolve eq30426 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30426
  have eq31172 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18858 y
       have i₂ := eq30431
       grind)
    | exact superpose eq30431 eq18858
    | exact resolve eq18858 eq30431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18858 eq30431
  have eq31195 : x = (M.op x y) ∨ x = y := by grind
  clear eq31172
  have eq31202 : x = (M.op x y) := by
    first
    | (have r₁ := eq31195
       have r₂ := eq9118
       grind)
    | exact resolve eq31195 eq9118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9118 eq31195
  have eq31326 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq26116
       have i₂ := eq31202
       grind)
    | exact superpose eq31202 eq26116
    | exact resolve eq26116 eq31202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26116
  have eq31344 : x = (M.op y y) := by grind
  clear eq31326
  have eq31451 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14604 y
       have i₂ := eq31344
       grind)
    | exact superpose eq31344 eq14604
    | exact resolve eq14604 eq31344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14604 eq31344
  have eq33799 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1313 y
       have i₂ := eq31451
       grind)
    | exact superpose eq31451 eq1313
    | exact resolve eq1313 eq31451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313 eq31451
  have eq33836 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq33799
  have eq33841 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq33836
       have r₂ := eq22534
       grind)
    | exact resolve eq33836 eq22534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22534 eq33836
  have eq34501 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33841
       grind)
    | exact superpose eq33841 eq14
    | exact resolve eq14 eq33841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33841
  have eq34557 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq34501
       have i₂ := eq31202
       grind)
    | exact superpose eq31202 eq34501
    | exact resolve eq34501 eq31202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31202 eq34501
  have eq34558 : False := by grind
  exact eq34558

/-- `Equation645`: `x = x ◇ (y ◇ ((y ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation645 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law645 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law645.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X0 := by
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
  have eq18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op x (M.op (M.op x x) X0))
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op X0 X0)
       have i₂ := eq18 X0 X0
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq34 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq24 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq44 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq40
    | exact resolve eq40 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq47 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq52 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
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
  have eq57 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq30 (τ X0) X1
       grind)
    | exact superpose eq30 eq17
    | (have j1 := eq30 (τ X0) X1
       grind)
    | exact resolve eq17 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq60 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44
    | exact resolve eq44 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq90 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq45 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq45
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq126 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq128 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq52
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq140 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq126 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq126
    | exact resolve eq126 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq210 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq24
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq24 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq140 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq140
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq140 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq140
  have eq304 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq285 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq285
    | (have j0 := eq285 X0 X1
       grind)
    | exact resolve eq285 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq815 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq846 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq10
    | (have j1 := eq47 X1 X0
       grind)
    | exact resolve eq10 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq905 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq815 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq815
    | (have j0 := eq815 X0 X1
       grind)
    | exact resolve eq815 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq930 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
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
  have eq981 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq930 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq930
    | (have j0 := eq930 X0 X1
       grind)
    | exact resolve eq930 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq1036 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1
       have i₂ := eq905 X0 X1
       grind)
    | (have i₁ := eq24 X0
       have i₂ := eq905 (M.op X0 X0) X1
       grind)
    | exact superpose eq905 eq24
    | (have j1 := eq905 X0 X1
       grind)
    | exact resolve eq24 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1364 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq24
    | (have j1 := eq55 X0 X0
       grind)
    | exact resolve eq24 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq55
  have eq2621 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq90
    | (have j0 := eq90 X1 (σ X0)
       grind)
    | exact resolve eq90 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq2692 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2621 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2621
    | (have j0 := eq2621 X0 X1
       grind)
    | exact resolve eq2621 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2621
  have eq2953 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq218 X0
       have i₂ := eq2692 X0 X0
       grind)
    | exact superpose eq2692 eq218
    | (have j0 := eq218 X0
       have j1 := eq2692 X0 X0
       grind)
    | (have r₁ := eq218 x
       have r₂ := eq2692 x x
       grind)
    | exact resolve eq218 eq2692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2692
  have eq2985 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2953 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2953
  have eq9280 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq304 x y
       grind)
    | exact superpose eq304 eq14
    | (have j1 := eq304 x y
       grind)
    | exact resolve eq14 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq9355 : y = (k y x) := by
    first
    | (have j1 := eq981 x y
       grind)
    | (have r₁ := eq9280
       have r₂ := eq981 x y
       grind)
    | exact resolve eq9280 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981 eq9280
  have eq10019 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35 x y
       have i₂ := eq9355
       grind)
    | exact superpose eq9355 eq35
    | (have j0 := eq35 x y
       grind)
    | exact resolve eq35 eq9355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq10022 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq905 x y
       have i₂ := eq9355
       grind)
    | exact superpose eq9355 eq905
    | (have j0 := eq905 x y
       grind)
    | exact resolve eq905 eq9355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq10023 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1036 x y
       have i₂ := eq9355
       grind)
    | exact superpose eq9355 eq1036
    | (have j0 := eq1036 x y
       grind)
    | exact resolve eq1036 eq9355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq11317 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18 x y
       have i₂ := eq10019
       grind)
    | exact superpose eq10019 eq18
    | exact resolve eq18 eq10019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq11348 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq14039 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11317
       have i₂ := eq10019
       grind)
    | exact superpose eq10019 eq11317
    | exact resolve eq11317 eq10019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10019 eq11317
  have eq14087 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14039
       have r₂ := eq11348
       grind)
    | exact resolve eq14039 eq11348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11348 eq14039
  have eq14362 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60 y y
       have i₂ := eq14087
       grind)
    | exact superpose eq14087 eq60
    | (have j0 := eq60 y y
       grind)
    | (have r₁ := eq60 y y
       have r₂ := eq14087
       grind)
    | exact resolve eq60 eq14087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq14087
  have eq14392 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq14362
  have eq14648 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq218 y
       have i₂ := eq14392
       grind)
    | exact superpose eq14392 eq218
    | (have j0 := eq218 y
       grind)
    | exact resolve eq218 eq14392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq14392
  have eq14670 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14648
  have eq34229 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq846 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq34230 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq34229 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34229
    | (have j0 := eq34229 X0
       grind)
    | exact resolve eq34229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34229
  have eq34371 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34230 X0
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq34230
    | (have j0 := eq34230 X0
       have j1 := eq30 X0 X0
       grind)
    | (have r₁ := eq34230 X0
       have r₂ := eq30 X0 X0
       grind)
    | exact resolve eq34230 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq34400 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq34371 X0
       have j1 := eq34230 X0
       grind)
    | (have r₁ := eq34371 X0
       have r₂ := eq34230 X0
       grind)
    | exact resolve eq34371 eq34230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34230 eq34371
  have eq34758 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq34400 (σ X0)
       have i₂ := eq2985 X0
       grind)
    | exact superpose eq2985 eq34400
    | (have j0 := eq34400 (σ X0)
       have j1 := eq2985 X0
       grind)
    | (have r₁ := eq34400 (σ X0)
       have r₂ := eq2985 X0
       grind)
    | exact resolve eq34400 eq2985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2985 eq34400
  have eq34770 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq34758 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34758
  have eq34783 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq34770 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34770
    | (have j0 := eq34770 X0
       grind)
    | exact resolve eq34770 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34770
  have eq40813 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq210 x y
       grind)
    | exact superpose eq210 eq14
    | (have j1 := eq210 x y
       grind)
    | exact resolve eq14 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40949 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq210 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq40980 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40813
       have i₂ := eq9355
       grind)
    | exact superpose eq9355 eq40813
    | exact resolve eq40813 eq9355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40813
  have eq42561 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq40949 (τ X1) (τ X0)
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq40949
    | (have j0 := eq40949 (τ X1) (τ X0)
       grind)
    | exact resolve eq40949 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq42569 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40949 x y
       have i₂ := eq9355
       grind)
    | exact superpose eq9355 eq40949
    | (have j0 := eq40949 x y
       grind)
    | exact resolve eq40949 eq9355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9355 eq40949
  have eq42625 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq42561 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq42561
    | (have j0 := eq42561 X0 X1
       grind)
    | exact resolve eq42561 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42561
  have eq42639 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq42625 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq42625
    | (have j0 := eq42625 X0 X1
       grind)
    | exact resolve eq42625 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42625
  have eq42643 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42639 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42639
    | (have j0 := eq42639 X0 X1
       grind)
    | exact resolve eq42639 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42639
  have eq42644 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42643 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42643
    | (have j0 := eq42643 X0 X1
       grind)
    | exact resolve eq42643 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42643
  have eq44680 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40980
       have i₂ := eq10023
       grind)
    | exact superpose eq10023 eq40980
    | (have r₁ := eq40980
       have r₂ := eq10023
       grind)
    | exact resolve eq40980 eq10023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44681 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40980
       have i₂ := eq10022
       grind)
    | exact superpose eq10022 eq40980
    | (have r₁ := eq40980
       have r₂ := eq10022
       grind)
    | exact resolve eq40980 eq10022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10022 eq40980
  have eq44683 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq44681
  have eq44684 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq44680
  have eq44740 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44683
       grind)
    | exact superpose eq44683 eq14
    | exact resolve eq14 eq44683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44683
  have eq45038 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44684
       grind)
    | exact superpose eq44684 eq14
    | exact resolve eq14 eq44684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45050 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128 (σ x) y
       have i₂ := eq44684
       grind)
    | exact superpose eq44684 eq128
    | (have j0 := eq128 (σ x) y
       grind)
    | exact resolve eq128 eq44684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq44684
  have eq45095 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45050
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq45050
    | exact resolve eq45050 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45050
  have eq45113 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq42644 y x
       grind)
    | (have r₁ := eq45095
       have r₂ := eq42644 y x
       grind)
    | exact resolve eq45095 eq42644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42644 eq45095
  have eq45281 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45038
       have i₂ := eq10023
       grind)
    | exact superpose eq10023 eq45038
    | exact resolve eq45038 eq10023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10023 eq45038
  have eq45285 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq45281
  have eq45533 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14670
       have i₂ := eq45113
       grind)
    | exact superpose eq45113 eq14670
    | exact resolve eq14670 eq45113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14670 eq45113
  have eq45617 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq45533
  have eq45642 : x = (M.op x y) := by
    first
    | (have r₁ := eq45617
       have r₂ := eq45285
       grind)
    | exact resolve eq45617 eq45285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45285 eq45617
  have eq45767 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44740
       have i₂ := eq45642
       grind)
    | exact superpose eq45642 eq44740
    | exact resolve eq44740 eq45642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44740
  have eq45838 : x = (M.op y y) := by grind
  clear eq45767
  have eq45913 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34783 y
       have i₂ := eq45838
       grind)
    | exact superpose eq45838 eq34783
    | exact resolve eq34783 eq45838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34783 eq45838
  have eq47080 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1364 y
       have i₂ := eq45913
       grind)
    | exact superpose eq45913 eq1364
    | exact resolve eq1364 eq45913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364 eq45913
  have eq47122 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq47080
  have eq47126 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq47122
       have r₂ := eq42569
       grind)
    | exact resolve eq47122 eq42569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42569 eq47122
  have eq47206 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq47126
       grind)
    | exact superpose eq47126 eq14
    | exact resolve eq14 eq47126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47126
  have eq47295 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq47206
       have i₂ := eq45642
       grind)
    | exact superpose eq45642 eq47206
    | exact resolve eq47206 eq45642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45642 eq47206
  have eq47296 : False := by grind
  exact eq47296

/-- `Equation645`: `x = x ◇ (y ◇ ((y ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation645 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law645 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law645.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op x (M.op (M.op x x) X0))
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op X0 X0)
       have i₂ := eq18 X0 X0
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq24 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq43 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  clear eq17
  have eq54 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq45 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq30
    | exact resolve eq30 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq30 (τ X0) X1
       grind)
    | exact superpose eq30 eq16
    | (have j1 := eq30 (τ X0) X1
       grind)
    | exact resolve eq16 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq63 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq43
    | exact resolve eq43 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq69 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq43
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq74 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq66
    | exact resolve eq66 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq124 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1
       have i₂ := eq12 X0 (τ X1)
       grind)
    | (have i₁ := eq54 X0
       have i₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq12 eq54
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq24
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq24 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq74
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq74 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq74
  have eq304 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq285 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq285
    | (have j0 := eq285 X0 X1
       grind)
    | exact resolve eq285 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq815 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq40
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq846 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq10
    | (have j1 := eq40 X1 X0
       grind)
    | exact resolve eq10 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq905 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq815 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq815
    | (have j0 := eq815 X0 X1
       grind)
    | exact resolve eq815 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq930 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
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
  have eq981 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq930 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq930
    | (have j0 := eq930 X0 X1
       grind)
    | exact resolve eq930 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq1036 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1
       have i₂ := eq905 X0 X1
       grind)
    | (have i₁ := eq24 X0
       have i₂ := eq905 (M.op X0 X0) X1
       grind)
    | exact superpose eq905 eq24
    | (have j1 := eq905 X0 X1
       grind)
    | exact resolve eq24 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1364 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (σ x)
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq24
    | (have j1 := eq55 X0 X0
       grind)
    | exact resolve eq24 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq55
  have eq8326 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq304 x y
       grind)
    | exact superpose eq304 eq14
    | (have j1 := eq304 x y
       grind)
    | exact resolve eq14 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq8396 : y = (k x y) := by
    first
    | (have j1 := eq981 x y
       grind)
    | (have r₁ := eq8326
       have r₂ := eq981 x y
       grind)
    | exact resolve eq8326 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981 eq8326
  have eq8592 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35 x y
       have i₂ := eq8396
       grind)
    | exact superpose eq8396 eq35
    | (have j0 := eq35 x y
       grind)
    | exact resolve eq35 eq8396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq8595 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq905 x y
       have i₂ := eq8396
       grind)
    | exact superpose eq8396 eq905
    | (have j0 := eq905 x y
       grind)
    | exact resolve eq905 eq8396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq8596 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1036 x y
       have i₂ := eq8396
       grind)
    | exact superpose eq8396 eq1036
    | (have j0 := eq1036 x y
       grind)
    | exact resolve eq1036 eq8396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq9877 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18 x y
       have i₂ := eq8592
       grind)
    | exact superpose eq8592 eq18
    | exact resolve eq18 eq8592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq9908 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq12917 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9877
       have i₂ := eq8592
       grind)
    | exact superpose eq8592 eq9877
    | exact resolve eq9877 eq8592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8592 eq9877
  have eq12963 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12917
       have r₂ := eq9908
       grind)
    | exact resolve eq12917 eq9908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9908 eq12917
  have eq13664 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60 y y
       have i₂ := eq12963
       grind)
    | exact superpose eq12963 eq60
    | (have j0 := eq60 y y
       grind)
    | (have r₁ := eq60 y y
       have r₂ := eq12963
       grind)
    | exact resolve eq60 eq12963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq12963
  have eq13690 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq13664
  have eq13967 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq218 y
       have i₂ := eq13690
       grind)
    | exact superpose eq13690 eq218
    | (have j0 := eq218 y
       grind)
    | exact resolve eq218 eq13690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq13690
  have eq13989 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13967
  have eq34022 : ∀ X0 : G, (k X0 (σ (τ X0))) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq846 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq34023 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq34022 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34022
    | (have j0 := eq34022 X0
       grind)
    | exact resolve eq34022 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34022
  have eq34124 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq34023 (σ X0)
       have i₂ := eq124 X0 (σ X0)
       grind)
    | exact superpose eq124 eq34023
    | (have j0 := eq34023 (σ X0)
       have j1 := eq124 X0 (σ X0)
       grind)
    | (have r₁ := eq34023 (σ X0)
       have r₂ := eq124 X0 (σ X0)
       grind)
    | exact resolve eq34023 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq34023
  have eq34131 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq34124 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34124
  have eq34134 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq34131 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34131
    | (have j0 := eq34131 X0
       grind)
    | exact resolve eq34131 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34131
  have eq34140 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq34134 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34134
    | (have j0 := eq34134 X0
       grind)
    | exact resolve eq34134 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34134
  have eq40533 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq210 x y
       grind)
    | exact superpose eq210 eq14
    | (have j1 := eq210 x y
       grind)
    | exact resolve eq14 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40666 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq210 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq40695 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40533
       have i₂ := eq8396
       grind)
    | exact superpose eq8396 eq40533
    | exact resolve eq40533 eq8396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40533
  have eq43490 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40666 (τ X0) (τ X1)
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq40666
    | (have j0 := eq40666 (τ X0) (τ X1)
       grind)
    | exact resolve eq40666 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq43505 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40666 x y
       have i₂ := eq8396
       grind)
    | exact superpose eq8396 eq40666
    | (have j0 := eq40666 x y
       grind)
    | exact resolve eq40666 eq8396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8396 eq40666
  have eq43575 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43490 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq43490
    | (have j0 := eq43490 X0 X1
       grind)
    | exact resolve eq43490 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43490
  have eq43585 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43575 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq43575
    | (have j0 := eq43575 X0 X1
       grind)
    | exact resolve eq43575 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43575
  have eq43586 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43585 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq43585
    | (have j0 := eq43585 X0 X1
       grind)
    | exact resolve eq43585 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43585
  have eq43587 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43586 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq43586
    | (have j0 := eq43586 X0 X1
       grind)
    | exact resolve eq43586 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43586
  have eq46410 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40695
       have i₂ := eq8596
       grind)
    | exact superpose eq8596 eq40695
    | (have r₁ := eq40695
       have r₂ := eq8596
       grind)
    | exact resolve eq40695 eq8596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46411 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40695
       have i₂ := eq8595
       grind)
    | exact superpose eq8595 eq40695
    | (have r₁ := eq40695
       have r₂ := eq8595
       grind)
    | exact resolve eq40695 eq8595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8595 eq40695
  have eq46415 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq46411
  have eq46416 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq46410
  have eq46684 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq46415
       grind)
    | exact superpose eq46415 eq14
    | exact resolve eq14 eq46415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46415
  have eq49100 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq46416
       grind)
    | exact superpose eq46416 eq14
    | exact resolve eq14 eq46416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49119 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq69 (σ x) y
       have i₂ := eq46416
       grind)
    | exact superpose eq46416 eq69
    | (have j0 := eq69 (σ x) y
       grind)
    | exact resolve eq69 eq46416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq46416
  have eq49236 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq49119
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq49119
    | exact resolve eq49119 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49119
  have eq49257 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq43587 x y
       grind)
    | (have r₁ := eq49236
       have r₂ := eq43587 x y
       grind)
    | exact resolve eq49236 eq43587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43587 eq49236
  have eq49859 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq49100
       have i₂ := eq8596
       grind)
    | exact superpose eq8596 eq49100
    | exact resolve eq49100 eq8596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8596 eq49100
  have eq49865 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq49859
  have eq50540 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13989
       have i₂ := eq49257
       grind)
    | exact superpose eq49257 eq13989
    | exact resolve eq13989 eq49257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13989 eq49257
  have eq50703 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq50540
  have eq50737 : x = (M.op x y) := by
    first
    | (have r₁ := eq50703
       have r₂ := eq49865
       grind)
    | exact resolve eq50703 eq49865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49865 eq50703
  have eq50985 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46684
       have i₂ := eq50737
       grind)
    | exact superpose eq50737 eq46684
    | exact resolve eq46684 eq50737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46684
  have eq51085 : x = (M.op y y) := by grind
  clear eq50985
  have eq51384 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34140 y
       have i₂ := eq51085
       grind)
    | exact superpose eq51085 eq34140
    | exact resolve eq34140 eq51085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34140 eq51085
  have eq57839 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1364 y
       have i₂ := eq51384
       grind)
    | exact superpose eq51384 eq1364
    | exact resolve eq1364 eq51384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364 eq51384
  have eq57888 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq57839
  have eq57892 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq57888
       have r₂ := eq43505
       grind)
    | exact resolve eq57888 eq43505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43505 eq57888
  have eq58649 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq57892
       grind)
    | exact superpose eq57892 eq14
    | exact resolve eq14 eq57892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57892
  have eq58802 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq58649
       have i₂ := eq50737
       grind)
    | exact superpose eq50737 eq58649
    | exact resolve eq58649 eq50737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50737 eq58649
  have eq58803 : False := by grind
  exact eq58803

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_pxx_pyx_Equation646 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law646 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq116 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq120 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq116 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq116 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq116 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq116 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq144 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq120 (σ X1) (σ X0)
       grind)
    | exact superpose eq120 eq13
    | exact resolve eq13 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq144 X0 X1
       have i₂ := eq120 X1 X0
       grind)
    | exact superpose eq120 eq144
    | exact resolve eq144 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq144
  have eq1499 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq149 x y
       grind)
    | exact superpose eq149 eq14
    | (have r₁ := eq14
       have r₂ := eq149 x y
       grind)
    | exact resolve eq14 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq1519 : False := by grind
  exact eq1519

/-- `Equation647`: `x = x ◇ (y ◇ ((y ◇ z) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation647 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law647 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law647.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) = X0 := by
    intro X0 X1 X2
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
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X0 (M.op X1 (M.op (M.op X1 X2) X2))
       have i₂ := eq8 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq22 X0 x x X3
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq22
    | exact resolve eq22 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq23 X0 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq23 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq53 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq56 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq58 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq53 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq83 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq134 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 (M.op X1 X1)
       have i₂ := eq33 X1 (σ X0)
       grind)
    | exact superpose eq33 eq83
    | exact resolve eq83 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq231 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq55 X2 X0
       grind)
    | exact superpose eq55 eq23
    | (have j1 := eq55 X2 X0
       grind)
    | exact resolve eq23 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq406 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) ≠ (k X0 (M.op X1 X1)) ∨ (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X1 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq186
    | exact resolve eq186 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq413 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq186 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq415 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq406 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq435 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq413 (σ X0)
       grind)
    | exact superpose eq413 eq13
    | exact resolve eq13 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq435 X0
       have i₂ := eq413 X0
       grind)
    | exact superpose eq413 eq435
    | exact resolve eq435 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq561 : ∀ X0 X1 : G, (τ (k (σ X0) (M.op X1 X1))) = (k (τ (σ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) X0
       have i₂ := eq415 (σ X0) X1
       grind)
    | exact superpose eq415 eq20
    | exact resolve eq20 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq415
  have eq565 : ∀ X0 X1 : G, (k X0 X0) = (τ (k (σ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq561 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq561
    | exact resolve eq561 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq582 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq565 X0 X1
       have i₂ := eq83 X0 (M.op X1 X1)
       grind)
    | exact superpose eq83 eq565
    | exact resolve eq565 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq565
  have eq745 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq56
    | (have j0 := eq56 X0 X1
       grind)
    | exact resolve eq56 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq820 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq745 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq745
    | (have j0 := eq745 X0 X1
       grind)
    | exact resolve eq745 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq964 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq450 X0
       grind)
    | exact superpose eq450 eq23
    | exact resolve eq23 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq2240 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq231 y X0 x
       grind)
    | exact superpose eq231 eq14
    | (have j1 := eq231 y X0 x
       grind)
    | exact resolve eq14 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq49506 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq2240 X0
       have i₂ := eq820 x y
       grind)
    | exact superpose eq820 eq2240
    | (have j0 := eq2240 X0
       have j1 := eq820 X0 y
       grind)
    | (have r₁ := eq2240 X0
       have r₂ := eq820 x y
       grind)
    | exact resolve eq2240 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq2240
  have eq49507 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq49506 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49506
  have eq49656 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op X0 X0))) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq134 y X0
       have i₂ := eq49507 (σ y)
       grind)
    | exact superpose eq49507 eq134
    | exact resolve eq134 eq49507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq49507
  have eq49679 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq49656 x
       have i₂ := eq582 y x
       grind)
    | exact superpose eq582 eq49656
    | exact resolve eq49656 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq49656
  have eq49736 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq49679
       have i₂ := eq413 y
       grind)
    | exact superpose eq413 eq49679
    | exact resolve eq49679 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq49679
  have eq49750 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq49736
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq49736
    | exact resolve eq49736 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49736
  have eq49751 : y = (M.op y y) := by grind
  clear eq49750
  have eq49958 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 y X0
       have i₂ := eq49751
       grind)
    | exact superpose eq49751 eq23
    | exact resolve eq23 eq49751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq49998 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq964 y X0
       have i₂ := eq49751
       grind)
    | exact superpose eq49751 eq964
    | exact resolve eq964 eq49751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964 eq49751
  have eq54068 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq49998 (σ x)
       grind)
    | exact superpose eq49998 eq14
    | exact resolve eq14 eq49998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49998
  have eq54099 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq54068
       have i₂ := eq49958 x
       grind)
    | exact superpose eq49958 eq54068
    | exact resolve eq54068 eq49958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49958 eq54068
  have eq54100 : False := by grind
  exact eq54100

/-- `Equation647`: `x = x ◇ (y ◇ ((y ◇ z) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation647 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law647 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law647.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X0 (M.op X1 (M.op (M.op X1 X2) X2))
       have i₂ := eq8 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq22 X0 x x X3
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq22
    | exact resolve eq22 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq23 X0 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq23 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq37 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq33 X0 (τ X1)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq45 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq47 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq55 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq68 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq47 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq47 eq13
    | (have j1 := eq47 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq139 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq44 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq380 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq424 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq380
    | (have j0 := eq380 X0 X1
       grind)
    | exact resolve eq380 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq1035 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37 X1 X1
       have i₂ := eq424 X0 X1
       grind)
    | exact superpose eq424 eq37
    | (have j1 := eq424 X2 X0
       grind)
    | exact resolve eq37 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq424
  have eq1070 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq139 (M.op X0 X0)
       have i₂ := eq33 X0 (M.op X0 X0)
       grind)
    | exact superpose eq33 eq139
    | (have j0 := eq139 (M.op X0 X0)
       grind)
    | exact resolve eq139 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq1084 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq139 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq139
    | (have j0 := eq139 (τ X0)
       grind)
    | exact resolve eq139 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq139
  have eq1096 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1070 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1100 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1084 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1084
    | (have j0 := eq1084 X0
       grind)
    | exact resolve eq1084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1109 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1100 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1100
    | (have j0 := eq1100 X0
       grind)
    | exact resolve eq1100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1577 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ (M.op X0 X0)) X1
       have i₂ := eq1096 X0
       grind)
    | exact superpose eq1096 eq23
    | exact resolve eq23 eq1096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096
  have eq1639 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq68 x y X0
       grind)
    | exact superpose eq68 eq14
    | (have j1 := eq68 X0 y X0
       grind)
    | exact resolve eq14 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1694 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1639 X0
       have j1 := eq1035 y X0 x
       grind)
    | (have r₁ := eq1639 X0
       have r₂ := eq1035 y x x
       grind)
    | exact resolve eq1639 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035 eq1639
  have eq1730 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq55 X0 (σ y)
       have i₂ := eq1694 (σ X0)
       grind)
    | exact superpose eq1694 eq55
    | exact resolve eq55 eq1694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1694
  have eq1736 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1730 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1730
    | exact resolve eq1730 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq1856 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1109 y
       have i₂ := eq1736 y
       grind)
    | exact superpose eq1736 eq1109
    | (have j0 := eq1109 y
       grind)
    | (have r₁ := eq1109 y
       have r₂ := eq1736 y
       grind)
    | exact resolve eq1109 eq1736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109 eq1736
  have eq1871 : y = (M.op y y) := by grind
  clear eq1856
  have eq1954 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 y X0
       have i₂ := eq1871
       grind)
    | exact superpose eq1871 eq23
    | exact resolve eq23 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq2689 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1577 y X0
       have i₂ := eq1871
       grind)
    | exact superpose eq1871 eq1577
    | exact resolve eq1577 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1577 eq1871
  have eq2998 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2689 (σ x)
       grind)
    | exact superpose eq2689 eq14
    | exact resolve eq14 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689
  have eq3002 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2998
       have i₂ := eq1954 x
       grind)
    | exact superpose eq1954 eq2998
    | exact resolve eq2998 eq1954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954 eq2998
  have eq3003 : False := by grind
  exact eq3003

/-- `Equation653`: `x = x ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_pxx_pyx_Equation653 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law653 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law653.models_iff G M).mp hM
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
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq95 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq91 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq91 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq91 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq111 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq95 (σ X1) (σ X0)
       grind)
    | exact superpose eq95 eq13
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X1
       have i₂ := eq95 X1 X0
       grind)
    | exact superpose eq95 eq111
    | exact resolve eq111 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq111
  have eq1278 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq118 x y
       grind)
    | exact superpose eq118 eq14
    | (have r₁ := eq14
       have r₂ := eq118 x y
       grind)
    | exact resolve eq14 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1302 : False := by grind
  exact eq1302
