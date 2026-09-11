import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pxx_x_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq75 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) := by
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
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
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
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq95 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq125 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq589 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op (M.op x y) y))) = (M.op (M.op X1 (M.op y (M.op X0 (M.op (M.op x y) y)))) (M.op X0 (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y)))) = (M.op (M.op X1 (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))))) (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq610
    | exact resolve eq610 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq614 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq611
       have r₂ := eq27
       grind)
    | exact resolve eq611 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq616 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq614
    | exact resolve eq614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq618 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq616
    | exact resolve eq616 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq621 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq618 eq64
    | (have r₁ := eq64
       have r₂ := eq618
       grind)
    | exact resolve eq64 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq618 eq27
    | exact resolve eq27 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  have eq625 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq621
  have eq640 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X2 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq652 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq625 eq114
    | exact resolve eq114 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq625 eq82
    | exact resolve eq82 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq655 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq652
  have eq704 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq93 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq708 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq704 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq704 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq704 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq704 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq718 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq708 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq708
    | (have j0 := eq708 X0 X1
       grind)
    | exact resolve eq708 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq731 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ (M.op x y)) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq655 eq14
    | exact resolve eq14 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq862 : ∀ X0 : G, (M.op (σ y) (M.op (σ (M.op x y)) (σ y))) = (M.op X0 (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq655 eq640
    | exact resolve eq640 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq864 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq640 X1 x X3
       have i₂ := eq640 X1 x X0
       grind)
    | exact superpose eq640 eq640
    | exact resolve eq640 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq640 X1 x X0
       grind)
    | exact superpose eq640 eq14
    | exact resolve eq14 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq1194 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq862 eq731
    | exact resolve eq731 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq862
  have eq1220 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1194 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1409 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1220
    | (have j0 := eq1220 (σ x)
       grind)
    | exact resolve eq1220 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq1430 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq618 eq1409
    | exact resolve eq1409 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq1439 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1430
  have eq1440 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1439
       have r₂ := eq624
       grind)
    | exact resolve eq1439 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1441 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1440
    | exact resolve eq1440 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440
  have eq1489 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq618 eq1441
    | exact resolve eq1441 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618 eq1441
  have eq1498 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1489
  have eq1500 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1498
       have r₂ := eq624
       grind)
    | exact resolve eq1498 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624 eq1498
  have eq1504 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1500 eq653
    | exact resolve eq653 eq1500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq1505 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1500 eq655
    | exact resolve eq655 eq1500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq1500
  have eq1517 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1505
  have eq1518 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1504
  have eq1522 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1517
       have r₂ := eq623
       grind)
    | exact resolve eq1517 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq1517
  have eq1523 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1518
    | exact resolve eq1518 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq1525 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1523
       have r₂ := eq75
       grind)
    | exact resolve eq1523 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1530 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1522 eq76
    | (have r₁ := eq76
       have r₂ := eq1522
       grind)
    | exact resolve eq76 eq1522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1532 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1530
  have eq1586 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1525
       grind)
    | exact superpose eq1525 eq72
    | exact resolve eq72 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525
  have eq1594 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1586
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1586
    | exact resolve eq1586 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586
  have eq1652 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1594 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1653 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1652
  have eq1659 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1653
    | exact resolve eq1653 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653
  have eq1662 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1659
    | exact resolve eq1659 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659
  have eq1663 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1662
  have eq1668 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1663 eq64
    | (have r₁ := eq64
       have r₂ := eq1663
       grind)
    | exact resolve eq64 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq1663
  have eq1685 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1668
  have eq1916 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1685 eq1594
    | exact resolve eq1594 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594 eq1685
  have eq1921 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1916
  have eq1939 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1921 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1921
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1921
       grind)
    | exact resolve eq13 eq1921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq1945 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1939
  have eq2046 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1945 eq87
    | exact resolve eq87 eq1945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq1945
  have eq2050 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2046
    | exact resolve eq2046 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2046
  have eq2053 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq2050
       grind)
    | exact superpose eq2050 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2050
  have eq2054 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2053
  have eq2163 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1532 eq82
    | exact resolve eq82 eq1532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1532
  have eq2174 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq2163
    | exact resolve eq2163 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2163
  have eq2177 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2174
       have r₂ := eq75
       grind)
    | exact resolve eq2174 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq2174
  have eq2283 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq2177
       grind)
    | exact superpose eq2177 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq2177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177
  have eq2284 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2283
  have eq2288 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2284
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2284
    | exact resolve eq2284 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2284
  have eq2289 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq2288
  have eq2293 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2289
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2289
    | exact resolve eq2289 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2289
  have eq2295 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2293 eq26
    | exact resolve eq26 eq2293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2296 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2293 eq29
    | exact resolve eq29 eq2293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq2304 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2293 eq114
    | exact resolve eq114 eq2293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq2293
  have eq2375 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2304
  have eq2383 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq2296
    | exact resolve eq2296 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2296
  have eq2484 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2383 eq20
    | exact resolve eq20 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2514 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2484
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2484
    | exact resolve eq2484 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2484
  have eq2651 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2295 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq2295
       grind)
    | exact resolve eq13 eq2295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295
  have eq2659 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2651
       have r₂ := eq1522
       grind)
    | exact resolve eq2651 eq1522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522 eq2651
  have eq2791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2659 eq2375
    | exact resolve eq2375 eq2659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375 eq2659
  have eq2795 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2791
  have eq2798 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2795
       have r₂ := eq27
       grind)
    | exact resolve eq2795 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2795
  have eq2800 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2798 eq20
    | exact resolve eq20 eq2798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2803 : y ≠ y ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2798 eq63
    | (have r₁ := eq63
       have r₂ := eq2798
       grind)
    | exact resolve eq63 eq2798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq2805 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2798 eq125
    | exact resolve eq125 eq2798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq2808 : (σ (k y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2798 eq134
    | exact resolve eq134 eq2798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2818 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq2798
  have eq2819 : (k y x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq2803
  have eq2826 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2808
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq2808
    | exact resolve eq2808 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2808
  have eq2829 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2805 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq2805
    | exact resolve eq2805 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq2805
  have eq2832 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2800
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2800
    | exact resolve eq2800 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2800
  have eq2987 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq2819
       grind)
    | exact superpose eq2819 eq72
    | exact resolve eq72 eq2819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2819
  have eq3553 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq95 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95
    | (have j0 := eq95 y
       grind)
    | exact resolve eq95 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq3572 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3553
  have eq3577 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3572
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq3572
    | exact resolve eq3572 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq3572
  have eq3588 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq3577
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq3577 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3577
  have eq3641 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq135
    | (have j0 := eq135 (M.op x y)
       grind)
    | exact resolve eq135 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq3659 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3641
  have eq3662 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq134 eq3659
    | exact resolve eq3659 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq3659
  have eq3674 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq3662
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3662 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662
  have eq5863 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq50 eq589
    | exact resolve eq589 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq5990 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op X1 (M.op (σ y) (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (M.op (σ x) (σ y)) (σ y))))) (M.op (σ y) (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (M.op (σ x) (σ y)) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq590 eq14
    | exact resolve eq14 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq6001 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op X1 (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))))) (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))))) := by
    intro X1
    first
    | exact superpose eq598 eq5990
    | exact resolve eq5990 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq5990
  have eq6005 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op X1 (σ y)) (σ y)) := by
    intro X1
    first
    | exact superpose eq51 eq6001
    | exact resolve eq6001 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq6001
  have eq7043 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq707 x y
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq707
    | (have j0 := eq707 x y
       grind)
    | exact resolve eq707 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq707
  have eq7099 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7043
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7043
    | exact resolve eq7043 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7043
  have eq7164 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7099
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7099
    | exact resolve eq7099 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7099
  have eq7221 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7164
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7164
    | exact resolve eq7164 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7164
  have eq7269 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq7221
    | exact resolve eq7221 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7221
  have eq7307 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq7269
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7269
    | exact resolve eq7269 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7269
  have eq7337 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq7307
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7307
    | exact resolve eq7307 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7307
  have eq7353 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq7337
    | exact resolve eq7337 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7337
  have eq14208 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2826 eq3588
    | exact resolve eq3588 eq2826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826 eq3588
  have eq14371 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3674 eq14208
    | exact resolve eq14208 eq3674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3674 eq14208
  have eq14483 : y = (M.op y (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq883 y y
       have i₂ := eq2054
       grind)
    | exact superpose eq2054 eq883
    | exact resolve eq883 eq2054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054
  have eq14503 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14371 eq883
    | exact resolve eq883 eq14371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14722 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14371 eq6005
    | exact resolve eq6005 eq14371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6005 eq14371
  have eq15250 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14503 eq883
    | exact resolve eq883 eq14503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883 eq14503
  have eq15557 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15250 eq14722
    | exact resolve eq14722 eq15250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14722 eq15250
  have eq15591 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq15557
  have eq18386 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y (M.op y y))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2383 eq5863
    | exact resolve eq5863 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5863
  have eq18442 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y (M.op y y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18386 X0
       grind)
    | (have r₁ := eq18386 X0
       have r₂ := eq2818
       grind)
    | exact resolve eq18386 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18386
  have eq18957 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2514 eq7353
    | exact resolve eq7353 eq2514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2514 eq7353
  have eq18978 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18957
       have r₂ := eq2818
       grind)
    | exact resolve eq18957 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18957
  have eq18980 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18978
       have r₂ := eq27
       grind)
    | exact resolve eq18978 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18978
  have eq19587 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14483
       have i₂ := eq864 y y X0
       grind)
    | (have i₁ := eq14483
       have i₂ := eq864 X0 y y
       grind)
    | exact superpose eq864 eq14483
    | exact resolve eq14483 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14483
  have eq20088 : y = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50 sF0
       have i₂ := eq19587 sF0
       grind)
    | exact superpose eq19587 eq50
    | exact resolve eq50 eq19587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq19587
  have eq22387 : y = (M.op (M.op x y) (M.op y (M.op y y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18442 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18442
    | (have j0 := eq18442 x
       grind)
    | exact resolve eq18442 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18442
  have eq22474 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22387
       have i₂ := eq864 y y X0
       grind)
    | (have i₁ := eq22387
       have i₂ := eq864 X0 y y
       grind)
    | exact superpose eq864 eq22387
    | exact resolve eq22387 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864 eq22387
  have eq22645 : y = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22474 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22474
    | (have j0 := eq22474 x
       grind)
    | exact resolve eq22474 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22474
  have eq22739 : y = (M.op y (M.op x y)) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2383 eq22645
    | exact resolve eq22645 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22645
  have eq22769 : y = (M.op y (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq22739
  have eq22771 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22769
       have r₂ := eq2818
       grind)
    | exact resolve eq22769 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22769
  have eq22773 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22771
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22771
    | exact resolve eq22771 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22771
  have eq22776 : y = (M.op y y) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2383 eq22773
    | exact resolve eq22773 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383 eq22773
  have eq22813 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq22776
  have eq22815 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22813
       have r₂ := eq2818
       grind)
    | exact resolve eq22813 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2818 eq22813
  have eq22915 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2987
       have i₂ := eq22815
       grind)
    | exact superpose eq22815 eq2987
    | exact resolve eq2987 eq22815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2987
  have eq22927 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq22815
       grind)
    | exact superpose eq22815 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq22815
       grind)
    | exact resolve eq13 eq22815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22815
  have eq22954 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq22927
  have eq22961 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq22915
  have eq22967 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22961
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22961
    | exact resolve eq22961 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22961
  have eq22980 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq718 y y
       have i₂ := eq22954
       grind)
    | exact superpose eq22954 eq718
    | (have j0 := eq718 y y
       grind)
    | exact resolve eq718 eq22954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22954
  have eq22983 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22980
  have eq22984 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22983
  have eq22995 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22984
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22984
    | exact resolve eq22984 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22984
  have eq23029 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22967 eq2829
    | exact resolve eq2829 eq22967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2829 eq22967
  have eq23041 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq23029
  have eq23136 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2832 eq22995
    | exact resolve eq22995 eq2832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22995
  have eq23203 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq23136
  have eq23216 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23041 eq18980
    | exact resolve eq18980 eq23041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18980 eq23041
  have eq23231 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq23216
  have eq23234 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23231
       have r₂ := eq2832
       grind)
    | exact resolve eq23231 eq2832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2832 eq23231
  have eq23270 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23234 eq15591
    | exact resolve eq15591 eq23234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15591 eq23234
  have eq23287 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq23270
  have eq23309 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq23287
    | exact resolve eq23287 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23287
  have eq24499 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23309 eq23203
    | exact resolve eq23203 eq23309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23203 eq23309
  have eq24550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24499
  have eq24567 : x = (M.op x y) := by
    first
    | (have r₁ := eq24550
       have r₂ := eq27
       grind)
    | exact resolve eq24550 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24550
  have eq24571 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq24567 eq20
    | exact resolve eq20 eq24567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq24619 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq24567 eq20088
    | exact resolve eq20088 eq24567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20088
  have eq24630 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq24619
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24619
    | exact resolve eq24619 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24619
  have eq24666 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq24571
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24571
    | exact resolve eq24571 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24571
  have eq24667 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq24567 eq24630
    | exact resolve eq24630 eq24567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24630
  have eq24668 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24667
  have eq24695 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq24666 eq26
    | exact resolve eq26 eq24666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq24811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq24666 eq24668
    | exact resolve eq24668 eq24666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24668
  have eq24812 : x = y := by
    first
    | (have r₁ := eq24811
       have r₂ := eq27
       grind)
    | exact resolve eq24811 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24811
  have eq24816 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24812
       grind)
    | exact superpose eq24812 eq18
    | exact resolve eq18 eq24812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24817 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq24812
       grind)
    | exact superpose eq24812 eq24
    | exact resolve eq24 eq24812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq24812
  have eq24955 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24817
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24817
    | exact resolve eq24817 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24817
  have eq24956 : x = (M.op x x) := by
    first
    | exact superpose eq24567 eq24816
    | exact resolve eq24816 eq24567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24567 eq24816
  have eq24984 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24666 eq24955
    | exact resolve eq24955 eq24666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24955
  have eq25122 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq24984 eq24695
    | exact resolve eq24695 eq24984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24695 eq24984
  have eq25204 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq24956
       grind)
    | exact superpose eq24956 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq24956
       grind)
    | exact resolve eq13 eq24956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24956
  have eq25231 : x = (k x x) := by grind
  clear eq25204
  have eq25533 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq718 x x
       have i₂ := eq25231
       grind)
    | exact superpose eq25231 eq718
    | (have j0 := eq718 x x
       grind)
    | exact resolve eq718 eq25231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq25231
  have eq25536 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq25533
  have eq25537 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq25536
  have eq25548 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq25537
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25537
    | exact resolve eq25537 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq25537
  have eq25557 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq24666 eq25548
    | exact resolve eq25548 eq24666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24666 eq25548
  have eq25566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25122 eq25557
    | exact resolve eq25557 eq25122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25122 eq25557
  have eq25575 : False := by grind
  exact eq25575

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pyx_pxy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
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
  clear eq17
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X0))) = (k (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 (M.op X0 (M.op (M.op X1 X0) X0)) X0
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op (M.op x X0) X0)) X0
       have r₂ := eq9 X0 X0 x
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (M.op X0 (M.op (M.op X1 X0) X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq265 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq307 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq265 X1 x X0
       grind)
    | exact superpose eq265 eq9
    | exact resolve eq9 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 x
       have i₂ := eq265 X1 x X0
       grind)
    | exact superpose eq265 eq35
    | exact resolve eq35 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq265
  have eq354 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq307 X0 (M.op X0 X0)
       have i₂ := eq307 X0 X0
       grind)
    | exact superpose eq307 eq307
    | exact resolve eq307 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq415 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (M.op X1 (σ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X1 (M.op X1 (σ X0))) X0
       have i₂ := eq308 X1 (σ X0)
       grind)
    | exact superpose eq308 eq22
    | exact resolve eq22 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq418 : ∀ X0 X1 : G, (k (τ (M.op X1 (M.op X1 (σ X0)))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq415 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq415
    | exact resolve eq415 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq522 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq354 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq354 X0
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq354
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq354 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq550 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq522 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq552 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq550 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq550 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq550 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq575 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X0)) = (σ (k X1 (k (τ (M.op X2 (M.op X2 (σ X0)))) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (M.op X2 (M.op X2 (σ X0))) X0 X1
       have i₂ := eq308 X2 (σ X0)
       grind)
    | exact superpose eq308 eq20
    | exact resolve eq20 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq308
  have eq593 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X0)) = (σ (M.op (k (τ (M.op X2 (M.op X2 (σ X0)))) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq575 X0 X1 X2
       have i₂ := eq552 (k (τ (M.op X2 (M.op X2 (σ X0)))) X0) X1
       grind)
    | exact superpose eq552 eq575
    | exact resolve eq575 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq612 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq593 X0 X1 x
       have i₂ := eq418 X0 x
       grind)
    | exact superpose eq418 eq593
    | exact resolve eq593 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418 eq593
  have eq629 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq612 X0 X1
       have i₂ := eq552 (σ X0) (σ X1)
       grind)
    | exact superpose eq552 eq612
    | exact resolve eq612 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq612
  have eq1263 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq629 x y
       grind)
    | exact superpose eq629 eq16
    | (have r₁ := eq16
       have r₂ := eq629 x y
       grind)
    | exact resolve eq16 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq1284 : False := by grind
  exact eq1284

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_x_pxy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
  clear eq18
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 (M.op (M.op X2 X0) X0)) = (k (M.op X1 (M.op (M.op X2 X0) X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 (M.op (M.op X2 X0) X0)) X1
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op (M.op X2 X0) X0)) X0
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (k (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq2019 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2034 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2019 X1 x X3
       have i₂ := eq2019 X1 x X0
       grind)
    | exact superpose eq2019 eq2019
    | exact resolve eq2019 eq2019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2041 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq2019 X1 x X0
       grind)
    | exact superpose eq2019 eq9
    | exact resolve eq9 eq2019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2042 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X1
       have i₂ := eq2019 X0 X1 x
       grind)
    | exact superpose eq2019 eq308
    | exact resolve eq308 eq2019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq2049 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X0 (M.op X2 X0) X2
       have i₂ := eq2019 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq2019 eq63
    | exact resolve eq63 eq2019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019
  have eq2058 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2049 X0 X1 X2
       have i₂ := eq63 X0 X0 X1
       grind)
    | exact superpose eq63 eq2049
    | exact resolve eq2049 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2049
  have eq2068 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2041 X0 (M.op X0 X0)
       have i₂ := eq2041 X0 X0
       grind)
    | exact superpose eq2041 eq2041
    | exact resolve eq2041 eq2041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2089 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq2068 X0
       grind)
    | exact superpose eq2068 eq9
    | exact resolve eq9 eq2068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2091 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq2068 X0
       grind)
    | exact superpose eq2068 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq2068 X0
       grind)
    | exact resolve eq12 eq2068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2102 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq2091 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq2498 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2034 X1 (M.op X1 (M.op X0 X0)) X2
       have i₂ := eq2089 X0 X1
       grind)
    | exact superpose eq2089 eq2034
    | exact resolve eq2034 eq2089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089
  have eq2499 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2034 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq2041 X1 X0
       grind)
    | exact superpose eq2041 eq2034
    | exact resolve eq2034 eq2041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2548 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X2 X1) (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2041 X2 (M.op X2 X1)
       have i₂ := eq2034 X2 X1 X0
       grind)
    | (have i₁ := eq2041 X2 (M.op X2 X1)
       have i₂ := eq2034 X0 X1 X2
       grind)
    | exact superpose eq2034 eq2041
    | exact resolve eq2041 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2586 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2058 X0 X1 X0
       have i₂ := eq2068 X0
       grind)
    | exact superpose eq2068 eq2058
    | exact resolve eq2058 eq2068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058 eq2068
  have eq2649 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1 X2 X1
       have i₂ := eq2586 X0 X1
       grind)
    | exact superpose eq2586 eq62
    | exact resolve eq62 eq2586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2660 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X1 X0)
       have i₂ := eq2586 X0 X1
       grind)
    | exact superpose eq2586 eq12
    | (have j0 := eq12 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq2586 X0 X0
       grind)
    | exact resolve eq12 eq2586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2826 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 (σ X1)))) = (k (τ (M.op X0 (M.op X0 (σ X1)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op X0 (M.op X0 (σ X1))) X1
       have i₂ := eq2042 X0 (σ X1)
       grind)
    | exact superpose eq2042 eq23
    | exact resolve eq23 eq2042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq2875 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2499 X2 X1 X1
       have i₂ := eq2034 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq2499 X2 X1 X1
       have i₂ := eq2034 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq2034 eq2499
    | exact resolve eq2499 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4415 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X2 (M.op X0 (M.op X0 (M.op X1 (M.op X2 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2649 X2 X2 X1
       have i₂ := eq2034 X2 (M.op X1 (M.op X2 X2)) X0
       grind)
    | (have i₁ := eq2649 X2 X2 X1
       have i₂ := eq2034 X0 (M.op X1 (M.op X2 X2)) X2
       grind)
    | exact superpose eq2034 eq2649
    | exact resolve eq2649 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2034 eq2649
  have eq4511 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X2 (M.op X1 X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq4415 x X1 X2
       have i₂ := eq2498 X2 X1 x
       grind)
    | exact superpose eq2498 eq4415
    | exact resolve eq4415 eq2498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2498 eq4415
  have eq4665 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2875 X1 X0 X1
       have i₂ := eq4511 X0 X1
       grind)
    | (have i₁ := eq2875 X1 x x
       have i₂ := eq4511 X1 x
       grind)
    | exact superpose eq4511 eq2875
    | exact resolve eq2875 eq4511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2875
  have eq4673 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2041 X1 (M.op X0 X1)
       have i₂ := eq4511 X0 X1
       grind)
    | (have i₁ := eq2041 X1 (M.op x x)
       have i₂ := eq4511 X1 x
       grind)
    | exact superpose eq4511 eq2041
    | exact resolve eq2041 eq4511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041 eq4511
  have eq6228 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq272 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq272
    | (have j0 := eq272 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq272 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6264 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq272 X1 X0
       grind)
    | exact superpose eq272 eq10
    | (have j1 := eq272 X1 X0
       grind)
    | exact resolve eq10 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40075 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6228 x y
       grind)
    | exact superpose eq6228 eq16
    | (have j1 := eq6228 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq6228 x y
       grind)
    | exact resolve eq16 eq6228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6228
  have eq40230 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq40075
  have eq150095 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2102 (σ y)
       have i₂ := eq40230
       grind)
    | exact superpose eq40230 eq2102
    | exact resolve eq2102 eq40230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102
  have eq150159 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2586 (σ y) (σ y)
       have i₂ := eq40230
       grind)
    | exact superpose eq40230 eq2586
    | exact resolve eq2586 eq40230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40230
  have eq150264 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq150159
  have eq150303 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq150264
  have eq150357 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq150095
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq150095
       have r₂ := eq12 y x
       grind)
    | exact resolve eq150095 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150095
  have eq150398 : (σ y) = (σ (k y x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq150357
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq150357
    | exact resolve eq150357 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150357
  have eq150414 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14 eq150398
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq150398 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150398
  have eq237187 : (M.op x y) = (τ (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq150414
       grind)
    | exact superpose eq150414 eq10
    | exact resolve eq10 eq150414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150414
  have eq237372 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq237187
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq237187
    | exact resolve eq237187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237187
  have eq237380 : (M.op x y) = (k (M.op x y) y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2042 x y
       have i₂ := eq237372
       grind)
    | exact superpose eq237372 eq2042
    | exact resolve eq2042 eq237372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042
  have eq237508 : x ≠ y ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  have eq237579 : y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq237372 eq237380
    | exact resolve eq237380 eq237372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237380
  have eq348188 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq150303
       grind)
    | exact superpose eq150303 eq16
    | exact resolve eq16 eq150303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348205 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (M.op X0 (σ y))))) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2548 X0 (σ y) (σ x)
       have i₂ := eq150303
       grind)
    | exact superpose eq150303 eq2548
    | exact resolve eq2548 eq150303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2548 eq150303
  have eq348410 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq348205 x
       have i₂ := eq2499 (σ y) x (σ x)
       grind)
    | exact superpose eq2499 eq348205
    | exact resolve eq348205 eq2499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2499 eq348205
  have eq348418 : (σ x) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq237372 eq348188
    | exact resolve eq348188 eq237372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237372 eq348188
  have eq358249 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6264 y y
       have i₂ := eq348410
       grind)
    | exact superpose eq348410 eq6264
    | exact resolve eq6264 eq348410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6264 eq348410
  have eq358545 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq358249
  have eq358610 : (k y y) = (τ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq358545
       have r₂ := eq348418
       grind)
    | exact resolve eq358545 eq348418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348418 eq358545
  have eq358651 : x = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq358610
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq358610
    | exact resolve eq358610 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358610
  have eq358679 : x = y ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq358651 eq237579
    | exact resolve eq237579 eq358651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237579 eq358651
  have eq358715 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq358679
       have r₂ := eq237508
       grind)
    | exact resolve eq358679 eq237508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237508 eq358679
  have eq358798 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2586 y y
       have i₂ := eq358715
       grind)
    | exact superpose eq358715 eq2586
    | exact resolve eq2586 eq358715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358799 : x ≠ x ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2660 y y
       have i₂ := eq358715
       grind)
    | exact superpose eq358715 eq2660
    | exact resolve eq2660 eq358715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2660 eq358715
  have eq358954 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq358799
  have eq358955 : x = (M.op x y) := by grind
  clear eq358798
  have eq359003 : y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq358954
       have r₂ := eq12 y x
       grind)
    | exact resolve eq358954 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358954
  have eq359170 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq358955
       grind)
    | exact superpose eq358955 eq16
    | exact resolve eq16 eq358955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359222 : x = (M.op x (M.op y (M.op x (M.op y y)))) := by
    first
    | (have i₁ := eq4673 x y
       have i₂ := eq358955
       grind)
    | exact superpose eq358955 eq4673
    | exact resolve eq4673 eq358955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4673 eq358955
  have eq359381 : x = (M.op y y) := by
    first
    | (have i₁ := eq359222
       have i₂ := eq4665 x y
       grind)
    | exact superpose eq4665 eq359222
    | exact resolve eq359222 eq4665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4665 eq359222
  have eq359426 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq272 y x
       have i₂ := eq359003
       grind)
    | exact superpose eq359003 eq272
    | (have j0 := eq272 y x
       grind)
    | exact resolve eq272 eq359003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq359003
  have eq359428 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq359426
       have r₂ := eq359170
       grind)
    | exact resolve eq359426 eq359170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359426
  have eq875101 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq359170
       have i₂ := eq359428
       grind)
    | exact superpose eq359428 eq359170
    | exact resolve eq359170 eq359428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq875136 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2826 (σ x) y
       have i₂ := eq359428
       grind)
    | exact superpose eq359428 eq2826
    | exact resolve eq2826 eq359428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826
  have eq875453 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq359428 eq875136
    | exact resolve eq875136 eq359428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359428 eq875136
  have eq875523 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq875453
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq875453
    | exact resolve eq875453 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875453
  have eq875688 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq2586 (σ y) (σ y)
       have i₂ := eq875523
       grind)
    | exact superpose eq875523 eq2586
    | exact resolve eq2586 eq875523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586 eq875523
  have eq875927 : y = (k y y) := by
    first
    | (have r₁ := eq875688
       have r₂ := eq359170
       grind)
    | exact resolve eq875688 eq359170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875688
  have eq876031 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq875927
       grind)
    | exact superpose eq875927 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq875927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875927
  have eq876032 : y = (M.op y y) := by grind
  clear eq876031
  have eq876043 : x = y := by
    first
    | (have i₁ := eq876032
       have i₂ := eq359381
       grind)
    | exact superpose eq359381 eq876032
    | exact resolve eq876032 eq359381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359381 eq876032
  have eq876057 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq359170
       have i₂ := eq876043
       grind)
    | exact superpose eq876043 eq359170
    | exact resolve eq359170 eq876043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359170
  have eq876142 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq875101
       have i₂ := eq876043
       grind)
    | exact superpose eq876043 eq875101
    | exact resolve eq875101 eq876043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875101
  have eq876144 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq876142
       have i₂ := eq876043
       grind)
    | exact superpose eq876043 eq876142
    | exact resolve eq876142 eq876043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876043 eq876142
  have eq876145 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq876144
  have eq876180 : False := by grind
  exact eq876180

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_x_pxy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  clear eq17
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
  clear eq18
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 (M.op (M.op X2 X0) X0)) = (k (M.op X1 (M.op (M.op X2 X0) X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 (M.op (M.op X2 X0) X0)) X1
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op (M.op X2 X0) X0)) X0
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (k (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1240 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1257 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1240 X1 x X3
       have i₂ := eq1240 X1 x X0
       grind)
    | exact superpose eq1240 eq1240
    | exact resolve eq1240 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1264 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq1240 X1 x X0
       grind)
    | exact superpose eq1240 eq9
    | exact resolve eq9 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1265 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq479 X0 X1
       have i₂ := eq1240 X0 X1 x
       grind)
    | exact superpose eq1240 eq479
    | exact resolve eq479 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq1273 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 (M.op X2 X0) X2
       have i₂ := eq1240 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq1240 eq62
    | exact resolve eq62 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq1283 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1273 X0 X1 X2
       have i₂ := eq62 X0 X0 X1
       grind)
    | exact superpose eq62 eq1273
    | exact resolve eq1273 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq1294 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1264 X0 (M.op X0 X0)
       have i₂ := eq1264 X0 X0
       grind)
    | exact superpose eq1264 eq1264
    | exact resolve eq1264 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1316 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq1294 X0
       grind)
    | exact superpose eq1294 eq9
    | exact resolve eq9 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1318 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq1294 X0
       grind)
    | exact superpose eq1294 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq1294 X0
       grind)
    | exact resolve eq12 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1329 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq1318 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318
  have eq1335 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq1329 (σ X0)
       grind)
    | exact superpose eq1329 eq28
    | exact resolve eq28 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1329
  have eq1354 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1335 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1335
    | exact resolve eq1335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq1576 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1257 X1 (M.op X1 (M.op X0 X0)) X2
       have i₂ := eq1316 X0 X1
       grind)
    | exact superpose eq1316 eq1257
    | exact resolve eq1257 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1577 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1257 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq1264 X1 X0
       grind)
    | exact superpose eq1264 eq1257
    | exact resolve eq1257 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1629 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X2 X1) (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1264 X2 (M.op X2 X1)
       have i₂ := eq1257 X2 X1 X0
       grind)
    | (have i₁ := eq1264 X2 (M.op X2 X1)
       have i₂ := eq1257 X0 X1 X2
       grind)
    | exact superpose eq1257 eq1264
    | exact resolve eq1264 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1669 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1283 X0 X1 X0
       have i₂ := eq1294 X0
       grind)
    | exact superpose eq1294 eq1283
    | exact resolve eq1283 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283 eq1294
  have eq1733 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X0 X1 X2 X1
       have i₂ := eq1669 X0 X1
       grind)
    | exact superpose eq1669 eq61
    | exact resolve eq61 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1734 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1 X1
       have i₂ := eq1669 X0 X1
       grind)
    | exact superpose eq1669 eq62
    | exact resolve eq62 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1753 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1734 X1 X1
       have i₂ := eq1257 X1 X1 X0
       grind)
    | (have i₁ := eq1734 X1 X1
       have i₂ := eq1257 X0 X1 X1
       grind)
    | exact superpose eq1257 eq1734
    | exact resolve eq1734 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq1826 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1264 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq1753 X1 X0
       grind)
    | exact superpose eq1753 eq1264
    | exact resolve eq1264 eq1753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753
  have eq1916 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 (σ X1)))) = (k (τ (M.op X0 (M.op X0 (σ X1)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X0 (M.op X0 (σ X1))) X1
       have i₂ := eq1265 X0 (σ X1)
       grind)
    | exact superpose eq1265 eq22
    | exact resolve eq22 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1960 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1577 (M.op X1 X0) X1 X1
       have i₂ := eq1577 X0 X1 X1
       grind)
    | exact superpose eq1577 eq1577
    | exact resolve eq1577 eq1577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1961 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1577 X2 X1 X1
       have i₂ := eq1257 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq1577 X2 X1 X1
       have i₂ := eq1257 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq1257 eq1577
    | exact resolve eq1577 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1989 : ∀ X0 X1 X2 : G, (k X2 (τ (M.op X0 (M.op X0 (M.op X1 (M.op X1 (σ X2))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1354 X2
       have i₂ := eq1577 (σ X2) X1 X0
       grind)
    | exact superpose eq1577 eq1354
    | exact resolve eq1354 eq1577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq2400 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1961 X2 X0 (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))
       have i₂ := eq1826 X0 X1
       grind)
    | exact superpose eq1826 eq1961
    | exact resolve eq1961 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826
  have eq2517 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2400 X0 X1 X2
       have i₂ := eq1960 (M.op X0 X0) (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq1960 eq2400
    | exact resolve eq2400 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2400
  have eq2540 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2517 X0 X1 X2
       have i₂ := eq1960 X0 X0
       grind)
    | exact superpose eq1960 eq2517
    | exact resolve eq2517 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2517
  have eq2559 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2540 X0 X1 x
       have i₂ := eq1264 x X0
       grind)
    | exact superpose eq1264 eq2540
    | exact resolve eq2540 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540
  have eq3515 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X2 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2559 X1 X2
       have i₂ := eq1257 X1 X1 X0
       grind)
    | (have i₁ := eq2559 X1 X2
       have i₂ := eq1257 X0 X1 X1
       grind)
    | exact superpose eq1257 eq2559
    | exact resolve eq2559 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2559
  have eq3901 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X2 (M.op X0 (M.op X0 (M.op X1 (M.op X2 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1733 X2 X2 X1
       have i₂ := eq1257 X2 (M.op X1 (M.op X2 X2)) X0
       grind)
    | (have i₁ := eq1733 X2 X2 X1
       have i₂ := eq1257 X0 (M.op X1 (M.op X2 X2)) X2
       grind)
    | exact superpose eq1257 eq1733
    | exact resolve eq1733 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq3932 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = (M.op (M.op X1 (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1264 x (M.op X1 (M.op X0 (M.op X1 X1)))
       have i₂ := eq1733 X1 x X0
       grind)
    | exact superpose eq1733 eq1264
    | exact resolve eq1264 eq1733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1733
  have eq3988 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3932 X0 X1
       have i₂ := eq1669 (M.op X0 (M.op X1 X1)) X1
       grind)
    | exact superpose eq1669 eq3932
    | exact resolve eq3932 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669 eq3932
  have eq4004 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X2 (M.op X1 X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq3901 x X1 X2
       have i₂ := eq1576 X2 X1 x
       grind)
    | exact superpose eq1576 eq3901
    | exact resolve eq3901 eq1576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1576 eq3901
  have eq4040 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3988 X0 X1
       have i₂ := eq1960 (M.op X1 X1) X0
       grind)
    | exact superpose eq1960 eq3988
    | exact resolve eq3988 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3988
  have eq4075 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4040 X0 X1
       have i₂ := eq1960 X1 X1
       grind)
    | exact superpose eq1960 eq4040
    | exact resolve eq4040 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4040
  have eq4172 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1961 X1 X0 X1
       have i₂ := eq4004 X0 X1
       grind)
    | (have i₁ := eq1961 X1 x x
       have i₂ := eq4004 X1 x
       grind)
    | exact superpose eq4004 eq1961
    | exact resolve eq1961 eq4004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq4181 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1264 X1 (M.op X0 X1)
       have i₂ := eq4004 X0 X1
       grind)
    | (have i₁ := eq1264 X1 (M.op x x)
       have i₂ := eq4004 X1 x
       grind)
    | exact superpose eq4004 eq1264
    | exact resolve eq1264 eq4004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq7409 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4172 X0 (M.op X0 (M.op X0 X1))
       have i₂ := eq3515 X0 X1 X0
       grind)
    | exact superpose eq3515 eq4172
    | exact resolve eq4172 eq3515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3515
  have eq7576 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq451 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq451 X0 X1
       grind)
    | exact superpose eq451 eq13
    | (have j0 := eq13 (σ X0) (σ X0)
       have j1 := eq451 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq451 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq451 X0 X0
       grind)
    | exact resolve eq13 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7653 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq451 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7657 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7576 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7576
  have eq7669 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7657 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7657
    | (have j0 := eq7657 X0 X1
       grind)
    | exact resolve eq7657 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7657
  have eq7680 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7669 X0 X1
       have j1 := eq7653 X0 X1
       grind)
    | (have r₁ := eq7669 X0 X1
       have r₂ := eq7653 X0 X1
       grind)
    | (have r₁ := eq7669 X0 X0
       have r₂ := eq7653 X0 X1
       grind)
    | exact resolve eq7669 eq7653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7653 eq7669
  have eq10259 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))))) = (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq4075 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq4075 (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact superpose eq4075 eq4075
    | exact resolve eq4075 eq4075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4075
  have eq10568 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq10259 X0 X1
       have i₂ := eq4172 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq4172 eq10259
    | exact resolve eq10259 eq4172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10259
  have eq10654 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10568 X0 X1
       have i₂ := eq7409 X0 X0 X0
       grind)
    | exact superpose eq7409 eq10568
    | exact resolve eq10568 eq7409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7409 eq10568
  have eq20080 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1577 X1 X0 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq10654 (M.op X0 X1) X0
       grind)
    | exact superpose eq10654 eq1577
    | exact resolve eq1577 eq10654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10654
  have eq20281 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq20080 X1 X0
       have i₂ := eq1960 X0 X1
       grind)
    | exact superpose eq1960 eq20080
    | exact resolve eq20080 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20080
  have eq20448 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20281 X0 X1
       have i₂ := eq1316 X1 X0
       grind)
    | exact superpose eq1316 eq20281
    | exact resolve eq20281 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20281
  have eq32088 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7680 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7680
  have eq32800 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (M.op (M.op (σ X0) (σ X1)) (M.op (σ X0) (M.op (σ X0) (σ X1)))) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20448 (σ X1) (σ X0)
       have i₂ := eq451 X0 X1
       grind)
    | (have i₁ := eq20448 (σ X1) (σ X1)
       have i₂ := eq451 X0 X1
       grind)
    | exact superpose eq451 eq20448
    | (have j1 := eq451 X1 X0
       grind)
    | exact resolve eq20448 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq20448
  have eq33131 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (M.op (σ X0) (M.op (M.op (σ X0) (σ X1)) (M.op (σ X0) (σ X1)))) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32800 X0 X1
       have i₂ := eq4004 (σ X0) (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq4004 eq32800
    | (have j0 := eq32800 X0 X1
       grind)
    | exact resolve eq32800 eq4004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4004 eq32800
  have eq33294 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (M.op (σ X0) (M.op (σ X0) (M.op (σ X1) (σ X1)))) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33131 X0 X1
       have i₂ := eq1960 (σ X1) (σ X0)
       grind)
    | exact superpose eq1960 eq33131
    | (have j0 := eq33131 X0 X1
       grind)
    | exact resolve eq33131 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960 eq33131
  have eq33380 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33294 X0 X1
       have i₂ := eq1316 (σ X1) (σ X0)
       grind)
    | exact superpose eq1316 eq33294
    | (have j0 := eq33294 X0 X1
       grind)
    | exact resolve eq33294 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33294
  have eq33442 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq33380 X0 X1
       have j1 := eq32088 X1 X0
       grind)
    | (have r₁ := eq33380 X0 X1
       have r₂ := eq32088 X0 X1
       grind)
    | (have r₁ := eq33380 X1 X0
       have r₂ := eq32088 X0 X1
       grind)
    | exact resolve eq33380 eq32088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32088 eq33380
  have eq33996 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq33442 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33442
  have eq34019 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq33996 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33996
  have eq34224 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq34019 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34019
  have eq34285 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq34224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34224
  have eq34703 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq34285 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34285
  have eq35710 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq34703 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34703
  have eq35766 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35710 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35710
  have eq36516 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35766 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35766
  have eq36792 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36516 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36516
  have eq37197 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36792 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36792
  have eq37888 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq37197 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37197
  have eq38551 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq37888 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37888
  have eq38876 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq38551 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38551
  have eq38902 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq38876 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq38876
    | (have j0 := eq38876 (τ X1) (τ X0)
       grind)
    | exact resolve eq38876 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq38982 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq38902 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38902
    | (have j0 := eq38902 X0 X1
       grind)
    | exact resolve eq38902 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38902
  have eq39004 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq38982 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq38982
    | (have j0 := eq38982 X0 X1
       grind)
    | exact resolve eq38982 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38982
  have eq39013 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39004 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq39004
    | (have j0 := eq39004 X0 X1
       grind)
    | exact resolve eq39004 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39004
  have eq39021 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39013 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39013
    | (have j0 := eq39013 X0 X1
       grind)
    | exact resolve eq39013 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39013
  have eq39028 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39021 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39021
    | (have j0 := eq39021 X0 X1
       grind)
    | exact resolve eq39021 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39021
  have eq39061 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38876 X0 X1
       have i₂ := eq39028 X1 X0
       grind)
    | exact superpose eq39028 eq38876
    | (have j0 := eq38876 X0 X1
       have j1 := eq39028 (σ X1) (σ X0)
       grind)
    | exact resolve eq38876 eq39028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262512 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq39061 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39061
  have eq262538 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq262512 x y
       grind)
    | exact superpose eq262512 eq16
    | (have j1 := eq262512 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq262512 x y
       grind)
    | exact resolve eq16 eq262512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262512
  have eq262788 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq262538
  have eq262829 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq262788
       grind)
    | exact superpose eq262788 eq16
    | exact resolve eq16 eq262788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262834 : ∀ X0 : G, y = (k y (τ (M.op X0 (M.op X0 (M.op (σ x) (σ x)))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1989 X0 (σ x) y
       have i₂ := eq262788
       grind)
    | exact superpose eq262788 eq1989
    | exact resolve eq1989 eq262788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989
  have eq262847 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (M.op X0 (σ y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1629 X0 (σ y) (σ x)
       have i₂ := eq262788
       grind)
    | exact superpose eq262788 eq1629
    | exact resolve eq1629 eq262788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1629 eq262788
  have eq263043 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq262847 x
       have i₂ := eq1577 (σ y) x (σ x)
       grind)
    | exact superpose eq1577 eq262847
    | exact resolve eq262847 eq1577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1577 eq262847
  have eq263048 : y = (k y (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq262834 x
       have i₂ := eq1316 (σ x) x
       grind)
    | exact superpose eq1316 eq262834
    | exact resolve eq262834 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316 eq262834
  have eq263066 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq263048
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq263048
    | exact resolve eq263048 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263048
  have eq263071 : y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq263066
       have r₂ := eq12 y x
       grind)
    | exact resolve eq263066 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263066
  have eq263073 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq263071
       have i₂ := eq39028 y x
       grind)
    | exact superpose eq39028 eq263071
    | (have j1 := eq39028 y x
       grind)
    | exact resolve eq263071 eq39028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39028
  have eq263075 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38876 x y
       have i₂ := eq263071
       grind)
    | exact superpose eq263071 eq38876
    | (have j0 := eq38876 x y
       grind)
    | exact resolve eq38876 eq263071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38876 eq263071
  have eq263081 : (M.op x y) = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1265 x y
       have i₂ := eq263073
       grind)
    | exact superpose eq263073 eq1265
    | exact resolve eq1265 eq263073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq263305 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq263073 eq263081
    | exact resolve eq263081 eq263073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263081
  have eq263764 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq263073 eq262829
    | exact resolve eq262829 eq263073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262829 eq263073
  have eq264750 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ y)
       have i₂ := eq263043
       grind)
    | exact superpose eq263043 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq263043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263043
  have eq264908 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq264750
  have eq264940 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq264908
       have r₂ := eq263764
       grind)
    | exact resolve eq264908 eq263764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264908
  have eq264963 : (σ x) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq264940
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq264940
    | exact resolve eq264940 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264940
  have eq264973 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq263305 eq264963
    | exact resolve eq264963 eq263305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263305 eq264963
  have eq264980 : x = (M.op x y) := by
    first
    | (have r₁ := eq264973
       have r₂ := eq263764
       grind)
    | exact resolve eq264973 eq263764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263764 eq264973
  have eq265668 : x = (M.op x y) := by grind
  clear eq264980
  have eq265900 : x = (M.op x y) := by grind
  clear eq265668
  have eq266530 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq265900
       grind)
    | exact superpose eq265900 eq16
    | exact resolve eq16 eq265900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266584 : x = (M.op x (M.op y (M.op x (M.op y y)))) := by
    first
    | (have i₁ := eq4181 x y
       have i₂ := eq265900
       grind)
    | exact superpose eq265900 eq4181
    | exact resolve eq4181 eq265900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4181 eq265900
  have eq266730 : x = (M.op y y) := by
    first
    | (have i₁ := eq266584
       have i₂ := eq4172 x y
       grind)
    | exact superpose eq4172 eq266584
    | exact resolve eq266584 eq4172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4172 eq266584
  have eq266837 : x ≠ x ∨ x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq266730
       grind)
    | exact superpose eq266730 eq13
    | exact resolve eq13 eq266730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266730
  have eq266991 : x = (k y y) ∨ x = y := by grind
  clear eq266837
  have eq485497 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq263075
       have r₂ := eq266530
       grind)
    | exact resolve eq263075 eq266530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263075
  have eq485498 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq266530
       have i₂ := eq485497
       grind)
    | exact superpose eq485497 eq266530
    | exact resolve eq266530 eq485497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266530
  have eq485508 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) := by
    first
    | (have i₁ := eq1916 (σ x) y
       have i₂ := eq485497
       grind)
    | exact superpose eq485497 eq1916
    | exact resolve eq1916 eq485497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1916
  have eq485758 : (τ (σ y)) = (k (τ (σ y)) y) := by
    first
    | (have i₁ := eq485508
       have i₂ := eq485497
       grind)
    | exact superpose eq485497 eq485508
    | exact resolve eq485508 eq485497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485497 eq485508
  have eq485802 : y = (k y y) := by
    first
    | (have i₁ := eq485758
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq485758
    | exact resolve eq485758 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485758
  have eq485811 : x = y ∨ x = y := by
    first
    | (have i₁ := eq266991
       have i₂ := eq485802
       grind)
    | exact superpose eq485802 eq266991
    | exact resolve eq266991 eq485802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266991 eq485802
  have eq485827 : x = y := by grind
  clear eq485811
  have eq485973 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq485498
       have i₂ := eq485827
       grind)
    | exact superpose eq485827 eq485498
    | exact resolve eq485498 eq485827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485498 eq485827
  have eq485975 : False := by grind
  exact eq485975

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_x_pyy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  clear eq22
  have eq39 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 (M.op (M.op X2 X0) X0)) = (k (M.op X1 (M.op (M.op X2 X0) X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 (M.op (M.op X2 X0) X0)) X1
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op (M.op X2 X0) X0)) X0
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) = (M.op (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X1 (M.op (M.op X2 X0) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40 (M.op X1 (M.op (M.op X2 X0) X0)) X1 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq40
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq9 eq40
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) X1
       have i₂ := eq40 (M.op (M.op X1 X2) X2) X3 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq108 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq108
    | (have j0 := eq108 (σ X0)
       grind)
    | exact resolve eq108 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ X0)
       have i₂ := eq108 (σ X0)
       grind)
    | exact superpose eq108 eq28
    | (have j1 := eq108 (σ X0)
       grind)
    | exact resolve eq28 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq108
  have eq125 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq115 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq115
    | (have j0 := eq115 X0
       grind)
    | exact resolve eq115 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq253 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (k (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq382 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (M.op (σ (k X0 X0)) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq9
    | (have j1 := eq109 X0
       grind)
    | exact resolve eq9 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq419 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0)))) = (M.op X4 (M.op X4 (M.op (M.op X2 (M.op (M.op X3 X0) X0)) (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq39 (M.op X1 (M.op (M.op X2 X0) X0)) X1 X2 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq447 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq426 X1 x X3
       have i₂ := eq426 X1 x X0
       grind)
    | exact superpose eq426 eq426
    | exact resolve eq426 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq426 X1 x X0
       grind)
    | exact superpose eq426 eq9
    | exact resolve eq9 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq357 X0 X1
       have i₂ := eq426 X0 X1 x
       grind)
    | exact superpose eq426 eq357
    | exact resolve eq357 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 X0 (M.op X2 X0) X2
       have i₂ := eq426 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq426 eq40
    | exact resolve eq40 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X2 X0))) = (k (M.op (M.op X2 X0) (M.op (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X2 X0))) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq357 (M.op X2 X0) X2
       have i₂ := eq426 X0 X1 X2
       grind)
    | exact superpose eq426 eq357
    | exact resolve eq357 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq473 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq463 X0 X1 X2
       have i₂ := eq40 X0 X0 X1
       grind)
    | exact superpose eq40 eq463
    | exact resolve eq463 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq484 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq454 X0 (M.op X0 X0)
       have i₂ := eq454 X0 X0
       grind)
    | exact superpose eq454 eq454
    | exact resolve eq454 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 (M.op X0 (M.op X0 X1)) X1 X1
       have i₂ := eq454 X0 X1
       grind)
    | exact superpose eq454 eq40
    | exact resolve eq40 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq497 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq491 X1 X0 X2
       have i₂ := eq454 X0 X1
       grind)
    | exact superpose eq454 eq491
    | exact resolve eq491 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq506 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq484 X0
       grind)
    | exact superpose eq484 eq9
    | exact resolve eq9 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq447 X1 (M.op X1 (M.op X0 X0)) X2
       have i₂ := eq506 X0 X1
       grind)
    | exact superpose eq506 eq447
    | exact resolve eq447 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq664 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq447 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq454 X1 X0
       grind)
    | exact superpose eq454 eq447
    | exact resolve eq447 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X2 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq447 X2 (M.op X2 X1) X3
       have i₂ := eq447 X2 X1 X0
       grind)
    | (have i₁ := eq447 X2 (M.op X2 X1) X3
       have i₂ := eq447 X0 X1 X2
       grind)
    | exact superpose eq447 eq447
    | exact resolve eq447 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq473 X0 X1 X0
       have i₂ := eq484 X0
       grind)
    | exact superpose eq484 eq473
    | exact resolve eq473 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq838 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq253 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq253 X0 X1
       grind)
    | exact superpose eq253 eq13
    | (have j0 := eq13 (σ X0) (σ X0)
       have j1 := eq253 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq253 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq253 X0 X0
       grind)
    | exact resolve eq13 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq868 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq253 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq253 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq873 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq838 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq875 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq873 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq873
    | (have j0 := eq873 X0 X1
       grind)
    | exact resolve eq873 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq1348 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq664 (M.op X1 X0) X1 X1
       have i₂ := eq664 X0 X1 X1
       grind)
    | exact superpose eq664 eq664
    | exact resolve eq664 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1349 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq664 X2 X1 X1
       have i₂ := eq447 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq664 X2 X1 X1
       have i₂ := eq447 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq447 eq664
    | exact resolve eq664 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq1485 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1 X1
       have i₂ := eq756 X0 X1
       grind)
    | exact superpose eq756 eq66
    | exact resolve eq66 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1486 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1485 X0 x
       have i₂ := eq756 (M.op X0 X0) x
       grind)
    | exact superpose eq756 eq1485
    | exact resolve eq1485 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485
  have eq4049 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = (M.op (M.op X3 (M.op X0 (M.op X1 (M.op X0 X0)))) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq64 X0 X1 X1 X3
       have i₂ := eq756 X0 X1
       grind)
    | exact superpose eq756 eq64
    | exact resolve eq64 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq4135 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X2 (M.op X1 (M.op X0 X0))) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X3 (M.op X0 (M.op X1 (M.op X0 X0)))) (M.op X0 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq426 (M.op X1 (M.op X0 X0)) X2 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X0))))
       have i₂ := eq4049 X0 X1 X3
       grind)
    | exact superpose eq4049 eq426
    | exact resolve eq426 eq4049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4049
  have eq4177 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X2 (M.op X1 (M.op X0 X0))) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X0 (M.op X1 (M.op X0 X0))) (M.op X0 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4135 X0 X1 X2 x
       have i₂ := eq756 (M.op X0 (M.op X1 (M.op X0 X0))) x
       grind)
    | exact superpose eq756 eq4135
    | exact resolve eq4135 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4135
  have eq4224 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X2 (M.op X1 (M.op X0 X0))) (M.op X1 (M.op X0 X0)))) = (M.op X0 (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4177 X0 X1 X2
       have i₂ := eq1348 (M.op X1 (M.op X0 X0)) X0
       grind)
    | exact superpose eq1348 eq4177
    | exact resolve eq4177 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4177
  have eq4254 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X2 (M.op X1 (M.op X0 X0))) (M.op X1 (M.op X0 X0)))) = (M.op X0 (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4224 X0 X1 X2
       have i₂ := eq1348 (M.op X0 X0) X1
       grind)
    | exact superpose eq1348 eq4224
    | exact resolve eq4224 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4224
  have eq4275 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X2 (M.op X1 (M.op X0 X0))) (M.op X1 (M.op X0 X0)))) = (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4254 X0 X1 X2
       have i₂ := eq1486 X0
       grind)
    | exact superpose eq1486 eq4254
    | exact resolve eq4254 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486 eq4254
  have eq4286 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0)))) = (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4275 X0 X1 x
       have i₂ := eq756 (M.op X1 (M.op X0 X0)) x
       grind)
    | exact superpose eq756 eq4275
    | exact resolve eq4275 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4275
  have eq4291 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4286 X0 X1
       have i₂ := eq663 X0 X1 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq663 eq4286
    | exact resolve eq4286 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq4286
  have eq4311 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4291 X1 X2
       have i₂ := eq447 X1 X1 X0
       grind)
    | (have i₁ := eq4291 X1 X2
       have i₂ := eq447 X0 X1 X1
       grind)
    | exact superpose eq447 eq4291
    | exact resolve eq4291 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4684 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4311 X0 (M.op X0 X1) X1
       have i₂ := eq4311 X0 X1 X0
       grind)
    | exact superpose eq4311 eq4311
    | exact resolve eq4311 eq4311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5725 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2)) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X0 X1 X2 x
       have i₂ := eq756 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2)) x
       grind)
    | exact superpose eq756 eq70
    | exact resolve eq70 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq5726 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op (M.op X1 X2) X2) (M.op (M.op X1 X2) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5725 X0 X1 X2
       have i₂ := eq1348 (M.op (M.op X1 X2) X2) (M.op X0 (M.op (M.op X1 X2) X2))
       grind)
    | exact superpose eq1348 eq5725
    | exact resolve eq5725 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5725
  have eq5727 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5726 X0 X1 X2
       have i₂ := eq1348 X2 (M.op X1 X2)
       grind)
    | exact superpose eq1348 eq5726
    | exact resolve eq5726 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5726
  have eq5728 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X2)) (M.op (M.op X1 X2) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5727 X0 X1 X2
       have i₂ := eq756 X2 X1
       grind)
    | exact superpose eq756 eq5727
    | exact resolve eq5727 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5727
  have eq5773 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4684 X0 X1
       have i₂ := eq1348 X1 X0
       grind)
    | exact superpose eq1348 eq4684
    | exact resolve eq4684 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4684
  have eq6667 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X2)) (M.op X2 (M.op (M.op X1 X2) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5728 X0 X1 X2
       have i₂ := eq5773 (M.op X1 X2) X2
       grind)
    | exact superpose eq5773 eq5728
    | exact resolve eq5728 eq5773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5728
  have eq6668 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X2 X2)) (M.op X2 (M.op X2 X2))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq6667 X0 x X2
       have i₂ := eq756 X2 x
       grind)
    | exact superpose eq756 eq6667
    | exact resolve eq6667 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6667
  have eq6763 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X0 X0))
       have i₂ := eq6668 X1 X0
       grind)
    | exact superpose eq6668 eq12
    | (have j0 := eq12 (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X0 X0))
       grind)
    | exact resolve eq12 eq6668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9469 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0)))) = (M.op X4 (M.op X4 (M.op (M.op X2 (M.op X0 X0)) (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0))))))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq419 X0 X1 X2 X1 X4
       have i₂ := eq756 X0 X1
       grind)
    | exact superpose eq756 eq419
    | exact resolve eq419 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq10662 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1))))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6668 (M.op (M.op X2 (M.op X0 X0)) (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0))))) (M.op (M.op X2 (M.op X0 X0)) (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0)))))
       have i₂ := eq9469 X0 X1 X2 (M.op (M.op X2 (M.op X0 X0)) (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0)))))
       grind)
    | exact superpose eq9469 eq6668
    | exact resolve eq6668 eq9469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6668 eq9469
  have eq10743 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1))))) = (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X1 (M.op X2 (M.op X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10662 X0 X1 X2
       have i₂ := eq1348 (M.op X1 (M.op X2 (M.op X1 X1))) X0
       grind)
    | exact superpose eq1348 eq10662
    | exact resolve eq10662 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10662
  have eq10855 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1))))) = (M.op X0 (M.op X1 (M.op (M.op X2 (M.op X1 X1)) (M.op X2 (M.op X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10743 X0 X1 X2
       have i₂ := eq1348 (M.op X2 (M.op X1 X1)) X1
       grind)
    | exact superpose eq1348 eq10743
    | exact resolve eq10743 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10743
  have eq10946 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1))))) = (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10855 X0 X1 X2
       have i₂ := eq1348 (M.op X1 X1) X2
       grind)
    | exact superpose eq1348 eq10855
    | exact resolve eq10855 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10855
  have eq11017 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1))))) = (M.op X0 (M.op X1 (M.op X2 (M.op X1 (M.op (M.op X1 X1) X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10946 X0 X1 X2
       have i₂ := eq5773 (M.op X1 X1) X1
       grind)
    | exact superpose eq5773 eq10946
    | exact resolve eq10946 eq5773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10946
  have eq11085 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1))))) = (M.op X0 (M.op X1 (M.op X2 (M.op X1 (M.op X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11017 X0 X1 X2
       have i₂ := eq484 X1
       grind)
    | exact superpose eq484 eq11017
    | exact resolve eq11017 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11017
  have eq11147 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1))))) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11085 X0 X1 X2
       have i₂ := eq4291 X1 X2
       grind)
    | exact superpose eq4291 eq11085
    | exact resolve eq11085 eq4291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4291 eq11085
  have eq11580 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq875 X0 X1
       have j1 := eq868 X0 X1
       grind)
    | (have r₁ := eq875 X0 X1
       have r₂ := eq868 X0 X1
       grind)
    | (have r₁ := eq875 X0 X0
       have r₂ := eq868 X0 X0
       grind)
    | exact resolve eq875 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868 eq875
  have eq11581 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq11580 X0 X1
       have j1 := eq869 X0 X1
       grind)
    | (have r₁ := eq11580 X0 X1
       have r₂ := eq869 X0 X1
       grind)
    | (have r₁ := eq11580 X0 X0
       have r₂ := eq869 X0 X1
       grind)
    | exact resolve eq11580 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869 eq11580
  have eq11586 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11581 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11581
    | exact resolve eq11581 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11610 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11581 x y
       grind)
    | exact superpose eq11581 eq16
    | (have j1 := eq11581 x y
       grind)
    | exact resolve eq16 eq11581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11654 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (M.op X2 (σ X0)) (σ X0))) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq426 (σ X0) X2 (σ X1)
       have i₂ := eq11581 X1 X0
       grind)
    | exact superpose eq11581 eq426
    | (have j1 := eq11581 X1 X0
       grind)
    | exact resolve eq426 eq11581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq11697 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq11581 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11709 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11654 X0 X1 x
       have i₂ := eq756 (σ X0) x
       grind)
    | exact superpose eq756 eq11654
    | (have j0 := eq11654 X0 X1 x
       grind)
    | exact resolve eq11654 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11654
  have eq11722 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11586 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq11586
    | (have j0 := eq11586 X0 X1
       grind)
    | exact resolve eq11586 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq11586
  have eq16026 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11697 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq11697
    | (have j0 := eq11697 (τ X1) (τ X0)
       grind)
    | exact resolve eq11697 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16040 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16026 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq16026
    | (have j0 := eq16026 X0 X1
       grind)
    | exact resolve eq16026 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16026
  have eq16048 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16040 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq16040
    | (have j0 := eq16040 X0 X1
       grind)
    | exact resolve eq16040 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16040
  have eq16053 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16048 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16048
    | (have j0 := eq16048 X0 X1
       grind)
    | exact resolve eq16048 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16048
  have eq16054 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16053 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16053
    | (have j0 := eq16053 X0 X1
       grind)
    | exact resolve eq16053 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16053
  have eq16079 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11722 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11722
    | exact resolve eq11722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11722
  have eq20320 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11610
       have i₂ := eq16079 y x
       grind)
    | exact superpose eq16079 eq11610
    | (have j1 := eq16079 (σ y) (σ x)
       grind)
    | exact resolve eq11610 eq16079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11610
  have eq20323 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20320
  have eq20327 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20323
       grind)
    | exact superpose eq20323 eq16
    | exact resolve eq16 eq20323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20329 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq20323
       grind)
    | exact superpose eq20323 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq20323
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq20323
       grind)
    | exact resolve eq12 eq20323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20355 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1349 X0 (σ x) (σ y)
       have i₂ := eq20323
       grind)
    | exact superpose eq20323 eq1349
    | exact resolve eq1349 eq20323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20323
  have eq20382 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq20329
  have eq20390 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20355 x
       have i₂ := eq454 x (σ x)
       grind)
    | exact superpose eq454 eq20355
    | exact resolve eq20355 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20355
  have eq20401 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20382
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq20382
    | exact resolve eq20382 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20382
  have eq20413 : (k y x) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq20401
       grind)
    | exact superpose eq20401 eq10
    | exact resolve eq10 eq20401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20401
  have eq20449 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20413
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq20413
    | exact resolve eq20413 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20413
  have eq20450 : y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq20449
       have r₂ := eq12 y x
       grind)
    | exact resolve eq20449 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20449
  have eq20451 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20450
       have i₂ := eq16079 y x
       grind)
    | exact superpose eq16079 eq20450
    | (have j1 := eq16079 y x
       grind)
    | exact resolve eq20450 eq16079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16079
  have eq20455 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11697 x y
       have i₂ := eq20450
       grind)
    | exact superpose eq20450 eq11697
    | (have j0 := eq11697 x y
       grind)
    | exact resolve eq11697 eq20450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11697
  have eq20456 : x ≠ y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16054 y x
       have i₂ := eq20450
       grind)
    | exact superpose eq20450 eq16054
    | (have j0 := eq16054 y x
       grind)
    | exact resolve eq16054 eq20450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16054
  have eq20458 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20327
       have i₂ := eq20451
       grind)
    | exact superpose eq20451 eq20327
    | exact resolve eq20327 eq20451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20327
  have eq20469 : (M.op x y) = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq455 x y
       have i₂ := eq20451
       grind)
    | exact superpose eq20451 eq455
    | exact resolve eq455 eq20451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20521 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20458
       have r₂ := eq20456
       grind)
    | exact resolve eq20458 eq20456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20458
  have eq20743 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq125 y
       have i₂ := eq20390
       grind)
    | exact superpose eq20390 eq125
    | exact resolve eq125 eq20390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq20390
  have eq20873 : (k y y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20743
       have r₂ := eq20521
       grind)
    | exact resolve eq20743 eq20521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20521 eq20743
  have eq20881 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20873
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20873
    | exact resolve eq20873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20873
  have eq21533 : y = (k y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20469
       have i₂ := eq20451
       grind)
    | exact superpose eq20451 eq20469
    | exact resolve eq20469 eq20451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20451 eq20469
  have eq21547 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21533
       have r₂ := eq20456
       grind)
    | exact resolve eq21533 eq20456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21533
  have eq21698 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20881
       have i₂ := eq21547
       grind)
    | exact superpose eq21547 eq20881
    | exact resolve eq20881 eq21547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20881 eq21547
  have eq21713 : x = y ∨ x = (M.op x y) := by grind
  clear eq21698
  have eq21718 : x = (M.op x y) := by
    first
    | (have r₁ := eq21713
       have r₂ := eq20456
       grind)
    | exact resolve eq21713 eq20456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20456 eq21713
  have eq21722 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq21718
       grind)
    | exact superpose eq21718 eq9
    | exact resolve eq9 eq21718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21737 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 y))) = (M.op X1 (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq666 x y X1 X0
       have i₂ := eq21718
       grind)
    | exact superpose eq21718 eq666
    | exact resolve eq666 eq21718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq21749 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq1349 X0 x y
       have i₂ := eq21718
       grind)
    | exact superpose eq21718 eq1349
    | exact resolve eq1349 eq21718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq21753 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op X0 (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq4311 x y X0
       have i₂ := eq21718
       grind)
    | exact superpose eq21718 eq4311
    | exact resolve eq4311 eq21718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4311
  have eq21784 : x = (M.op y y) := by
    first
    | (have i₁ := eq21749 x
       have i₂ := eq454 x x
       grind)
    | exact superpose eq454 eq21749
    | exact resolve eq21749 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21749
  have eq21798 : ∀ X0 : G, y = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq21722 X0
       have i₂ := eq21718
       grind)
    | exact superpose eq21718 eq21722
    | exact resolve eq21722 eq21718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21722
  have eq21846 : x ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq21784
       grind)
    | exact superpose eq21784 eq12
    | (have j0 := eq12 y y
       grind)
    | exact resolve eq12 eq21784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21847 : x ≠ x ∨ x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq21784
       grind)
    | exact superpose eq21784 eq13
    | exact resolve eq13 eq21784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21903 : x = (k y y) ∨ x = y := by grind
  clear eq21847
  have eq22529 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op (M.op X0 x) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq756 (M.op X0 x) X0
       have i₂ := eq21798 X0
       grind)
    | exact superpose eq21798 eq756
    | exact resolve eq756 eq21798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22603 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq22529 X0
       have i₂ := eq1348 x X0
       grind)
    | exact superpose eq1348 eq22529
    | exact resolve eq22529 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22529
  have eq28775 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11147 X0 X1 X1
       have i₂ := eq447 X1 X1 x
       grind)
    | (have i₁ := eq11147 X0 X1 X1
       have i₂ := eq447 X0 X1 X1
       grind)
    | exact superpose eq447 eq11147
    | exact resolve eq11147 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq11147
  have eq29205 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28775 X0 X1 X2
       have i₂ := eq454 X0 X1
       grind)
    | exact superpose eq454 eq28775
    | exact resolve eq28775 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28775
  have eq30745 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (σ (k (τ X0) (τ X0))) X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq382 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq382
    | exact resolve eq382 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31035 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (k X0 (σ (τ X0))) X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30745 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq30745
    | (have j0 := eq30745 X0 X1
       grind)
    | exact resolve eq30745 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq30745
  have eq31123 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (k X0 X0) X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31035 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31035
    | (have j0 := eq31035 X0 X1
       grind)
    | exact resolve eq31035 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31035
  have eq36120 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq22603 X0
       have i₂ := eq5773 X0 x
       grind)
    | (have i₁ := eq22603 x
       have i₂ := eq5773 x x
       grind)
    | exact superpose eq5773 eq22603
    | exact resolve eq22603 eq5773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22603
  have eq38821 : ∀ X0 : G, (σ X0) ≠ (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6763 (M.op (σ (k X0 X0)) (σ X0)) (M.op (σ (k X0 X0)) (σ X0))
       have i₂ := eq382 X0 (M.op (σ (k X0 X0)) (σ X0))
       grind)
    | exact superpose eq382 eq6763
    | (have j1 := eq382 X0 x
       grind)
    | exact resolve eq6763 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq6763
  have eq38880 : ∀ X0 : G, (σ X0) ≠ (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq38821 X0
       have j1 := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq38821 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | exact resolve eq38821 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38821
  have eq38917 : ∀ X0 : G, (σ X0) ≠ (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38880 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq38880
    | (have j0 := eq38880 X0
       grind)
    | exact resolve eq38880 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38880
  have eq39020 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (M.op (σ (τ X0)) (σ (τ X0)))) = (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11709 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq11709
    | (have j0 := eq11709 (τ X0) (τ X1)
       grind)
    | exact resolve eq11709 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq11709
  have eq39323 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (M.op (σ (τ X0)) (σ (τ X0)))) = (M.op (σ (τ X1)) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39020 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq39020
    | (have j0 := eq39020 X0 X1
       grind)
    | exact resolve eq39020 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39020
  have eq39390 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (M.op (σ (τ X0)) (σ (τ X0)))) = (M.op X1 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39323 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq39323
    | (have j0 := eq39323 X0 X1
       grind)
    | exact resolve eq39323 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39323
  have eq39415 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39390 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39390
    | (have j0 := eq39390 X0 X1
       grind)
    | exact resolve eq39390 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39390
  have eq39425 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 (M.op X0 X0)) = (M.op X1 (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39415 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39415
    | (have j0 := eq39415 X0 X1
       grind)
    | exact resolve eq39415 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39415
  have eq39429 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (k X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39425 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39425
    | (have j0 := eq39425 X0 X1
       grind)
    | exact resolve eq39425 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39425
  have eq85376 : ∀ X0 X2 : G, (M.op (M.op X2 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X0))) = (k (M.op (M.op X2 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X0))) (M.op X2 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq472 X0 x X2
       have i₂ := eq756 X0 x
       grind)
    | exact superpose eq756 eq472
    | exact resolve eq472 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq85377 : ∀ X0 X2 : G, (M.op (M.op X2 X0) (M.op X2 (M.op X0 X0))) = (k (M.op (M.op X2 X0) (M.op X2 (M.op X0 X0))) (M.op X2 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq85376 x X2
       have i₂ := eq29205 x x X2
       grind)
    | exact superpose eq29205 eq85376
    | exact resolve eq85376 eq29205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29205 eq85376
  have eq85669 : ∀ X0 : G, (M.op (M.op X0 y) (M.op y (M.op (M.op X0 (M.op x x)) (M.op X0 (M.op x x))))) = (k (M.op (M.op X0 y) (M.op y (M.op (M.op X0 (M.op x x)) (M.op X0 (M.op x x))))) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq85377 (M.op X0 (M.op x x)) y
       have i₂ := eq21753 X0
       grind)
    | exact superpose eq21753 eq85377
    | exact resolve eq85377 eq21753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21753 eq85377
  have eq85696 : ∀ X0 : G, (M.op (M.op X0 y) (M.op y (M.op X0 (M.op (M.op x x) (M.op x x))))) = (k (M.op (M.op X0 y) (M.op y (M.op X0 (M.op (M.op x x) (M.op x x))))) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq85669 x
       have i₂ := eq1348 (M.op x x) x
       grind)
    | exact superpose eq1348 eq85669
    | exact resolve eq85669 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85669
  have eq85939 : ∀ X0 : G, (M.op (M.op X0 y) (M.op y (M.op X0 (M.op x (M.op (M.op x x) x))))) = (k (M.op (M.op X0 y) (M.op y (M.op X0 (M.op x (M.op (M.op x x) x))))) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq85696 X0
       have i₂ := eq5773 (M.op x x) x
       grind)
    | exact superpose eq5773 eq85696
    | exact resolve eq85696 eq5773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85696
  have eq86122 : ∀ X0 : G, (M.op (M.op X0 y) (M.op y (M.op X0 (M.op x (M.op x x))))) = (k (M.op (M.op X0 y) (M.op y (M.op X0 (M.op x (M.op x x))))) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq85939 X0
       have i₂ := eq484 x
       grind)
    | exact superpose eq484 eq85939
    | exact resolve eq85939 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484 eq85939
  have eq86239 : ∀ X0 : G, (M.op (M.op X0 y) (M.op y (M.op X0 y))) = (k (M.op (M.op X0 y) (M.op y (M.op X0 y))) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq86122 X0
       have i₂ := eq21798 x
       grind)
    | exact superpose eq21798 eq86122
    | exact resolve eq86122 eq21798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21798 eq86122
  have eq86308 : ∀ X0 : G, (M.op y (M.op (M.op X0 y) (M.op X0 y))) = (k (M.op y (M.op (M.op X0 y) (M.op X0 y))) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq86239 X0
       have i₂ := eq5773 y (M.op X0 y)
       grind)
    | exact superpose eq5773 eq86239
    | exact resolve eq86239 eq5773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86239
  have eq86350 : ∀ X0 : G, (M.op y (M.op X0 (M.op y y))) = (k (M.op y (M.op X0 (M.op y y))) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq86308 x
       have i₂ := eq1348 y x
       grind)
    | exact superpose eq1348 eq86308
    | exact resolve eq86308 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348 eq86308
  have eq86376 : ∀ X0 : G, (M.op y (M.op X0 x)) = (k (M.op y (M.op X0 x)) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq86350 X0
       have i₂ := eq21784
       grind)
    | exact superpose eq21784 eq86350
    | exact resolve eq86350 eq21784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86350
  have eq86387 : ∀ X0 : G, (M.op x (M.op X0 x)) = (k (M.op x (M.op X0 x)) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq86376 X0
       have i₂ := eq36120 X0
       grind)
    | exact superpose eq36120 eq86376
    | exact resolve eq86376 eq36120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36120 eq86376
  have eq311458 : y = (M.op (k y y) (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq21737 x (k y y)
       have i₂ := eq31123 y x
       grind)
    | exact superpose eq31123 eq21737
    | (have j1 := eq31123 y x
       grind)
    | exact resolve eq21737 eq31123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21737 eq31123
  have eq312236 : y = (M.op x (M.op (k y y) x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq311458
       have i₂ := eq5773 (k y y) x
       grind)
    | exact superpose eq5773 eq311458
    | exact resolve eq311458 eq5773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5773 eq311458
  have eq312651 : y = (M.op x (M.op (k y y) x)) ∨ x = y := by
    first
    | (have i₁ := eq312236
       have i₂ := eq21784
       grind)
    | exact superpose eq21784 eq312236
    | exact resolve eq312236 eq21784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312236
  have eq313953 : y = (k y (M.op (k y y) y)) ∨ x = y := by
    first
    | (have i₁ := eq86387 (k y y)
       have i₂ := eq312651
       grind)
    | exact superpose eq312651 eq86387
    | exact resolve eq86387 eq312651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86387 eq312651
  have eq353816 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (k X1 X0))) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq454 X1 X1
       have i₂ := eq39429 X1 X0
       grind)
    | exact superpose eq39429 eq454
    | (have j1 := eq39429 (M.op X0 (k X1 X0)) X1
       grind)
    | exact resolve eq454 eq39429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353818 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (k X1 X0))) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq497 X1 X1 X2
       have i₂ := eq39429 X1 X0
       grind)
    | exact superpose eq39429 eq497
    | (have j1 := eq39429 X1 X0
       grind)
    | exact resolve eq497 eq39429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497 eq39429
  have eq360175 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq454 X0 (k X0 X0)
       have i₂ := eq353816 X0 X0
       grind)
    | exact superpose eq353816 eq454
    | (have j1 := eq353816 (k X0 X0) X0
       grind)
    | exact resolve eq454 eq353816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq353816
  have eq515658 : ∀ X0 X1 : G, (k X0 (k X0 (M.op X1 X0))) = X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq455 (M.op x X1) (k X1 (M.op x X1))
       have i₂ := eq353818 (M.op x X1) X1 x
       grind)
    | exact superpose eq353818 eq455
    | (have j1 := eq353818 (M.op X1 X0) X0 x
       grind)
    | exact resolve eq455 eq353818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq353818
  have eq516137 : ∀ X0 X1 : G, (k X0 (k X0 (M.op X1 X0))) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq515658 X0 X1
       have i₂ := eq756 X0 X1
       grind)
    | exact superpose eq756 eq515658
    | (have j0 := eq515658 X0 X1
       grind)
    | exact resolve eq515658 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq515658
  have eq530223 : y = (k y y) ∨ (M.op y y) = (M.op (k y y) y) ∨ x = y := by
    first
    | (have i₁ := eq516137 y (k y y)
       have i₂ := eq313953
       grind)
    | exact superpose eq313953 eq516137
    | (have j0 := eq516137 y (k y y)
       grind)
    | exact resolve eq516137 eq313953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313953 eq516137
  have eq530378 : y = (k y y) ∨ (M.op y y) = (M.op (k y y) y) := by
    first
    | (have r₁ := eq530223
       have r₂ := eq21846
       grind)
    | exact resolve eq530223 eq21846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21846 eq530223
  have eq530609 : x = (M.op (k y y) y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq530378
       have i₂ := eq21784
       grind)
    | exact superpose eq21784 eq530378
    | exact resolve eq530378 eq21784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21784 eq530378
  have eq531049 : x = (k y y) ∨ y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq530609
       have i₂ := eq360175 y
       grind)
    | exact superpose eq360175 eq530609
    | (have j1 := eq360175 y
       grind)
    | exact resolve eq530609 eq360175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360175 eq530609
  have eq531434 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have j1 := eq12 y y
       grind)
    | (have r₁ := eq531049
       have r₂ := eq12 y y
       grind)
    | exact resolve eq531049 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531049
  have eq531840 : x ≠ y ∨ x = (k y y) := by grind
  clear eq531434
  have eq531859 : x = (k y y) := by
    first
    | (have r₁ := eq531840
       have r₂ := eq21903
       grind)
    | exact resolve eq531840 eq21903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21903 eq531840
  have eq532021 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq38917 y
       have i₂ := eq531859
       grind)
    | exact superpose eq531859 eq38917
    | exact resolve eq38917 eq531859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38917 eq531859
  have eq532130 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq532021
       have i₂ := eq11581 x y
       grind)
    | exact superpose eq11581 eq532021
    | (have j1 := eq11581 x y
       grind)
    | exact resolve eq532021 eq11581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11581 eq532021
  have eq532134 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq532130
       have r₂ := eq20455
       grind)
    | exact resolve eq532130 eq20455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20455 eq532130
  have eq532137 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq532134
       have i₂ := eq20450
       grind)
    | exact superpose eq20450 eq532134
    | exact resolve eq532134 eq20450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20450 eq532134
  have eq532138 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq532137
  have eq532143 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq532138
       grind)
    | exact superpose eq532138 eq16
    | exact resolve eq16 eq532138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532138
  have eq532380 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq532143
       have i₂ := eq21718
       grind)
    | exact superpose eq21718 eq532143
    | exact resolve eq532143 eq21718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21718 eq532143
  have eq532381 : False := by grind
  exact eq532381

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq47 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq30 X1 (τ X0)
       grind)
    | exact superpose eq30 eq19
    | (have j1 := eq30 X1 (τ X0)
       grind)
    | exact resolve eq19 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq30 (σ X1) (σ X0)
       grind)
    | exact superpose eq30 eq15
    | (have j1 := eq30 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq30 X1 X0
       grind)
    | exact superpose eq30 eq25
    | (have j0 := eq25 X0 X1
       have j1 := eq30 (σ X1) (σ X0)
       grind)
    | exact resolve eq25 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq30
  have eq184 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq67 X1 x X3
       have i₂ := eq67 X1 x X0
       grind)
    | exact superpose eq67 eq67
    | exact resolve eq67 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq67 X1 x X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq388 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47
    | exact resolve eq47 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq407 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq388
    | (have j0 := eq388 X0 X1
       grind)
    | exact resolve eq388 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq444 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq945 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq16
    | (have j1 := eq83 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq83 x y
       grind)
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1015 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq945
  have eq1417 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1015
       grind)
    | exact superpose eq1015 eq16
    | exact resolve eq16 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1419 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq1015
       grind)
    | exact superpose eq1015 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1015
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1015
       grind)
    | exact resolve eq13 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1427 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1419
  have eq1428 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1427
  have eq1430 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1428
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1428
    | exact resolve eq1428 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428
  have eq6415 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq407 x y
       have i₂ := eq1430
       grind)
    | exact superpose eq1430 eq407
    | (have j0 := eq407 x y
       grind)
    | exact resolve eq407 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq6465 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq6415
  have eq6476 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq6465
       have r₂ := eq1417
       grind)
    | exact resolve eq6465 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417 eq6465
  have eq9393 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq6476
  have eq9453 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9393
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9393
    | exact resolve eq9393 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9393
  have eq13520 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq407 x y
       have i₂ := eq9453
       grind)
    | exact superpose eq9453 eq407
    | (have j0 := eq407 x y
       grind)
    | exact resolve eq407 eq9453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407 eq9453
  have eq13620 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13520
  have eq13626 : y = (M.op x y) := by
    first
    | (have r₁ := eq13620
       have r₂ := eq16
       grind)
    | exact resolve eq13620 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13620
  have eq17595 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq13626
       grind)
    | exact superpose eq13626 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq13626
       grind)
    | exact resolve eq13 eq13626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17614 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq184 X0 y x
       have i₂ := eq13626
       grind)
    | exact superpose eq13626 eq184
    | exact resolve eq184 eq13626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq17635 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq17595
  have eq17644 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq17614 X0
       have i₂ := eq13626
       grind)
    | exact superpose eq13626 eq17614
    | exact resolve eq17614 eq13626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17614
  have eq178598 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq48 x y
       have i₂ := eq17635
       grind)
    | exact superpose eq17635 eq48
    | (have j0 := eq48 x y
       grind)
    | exact resolve eq48 eq17635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq17635
  have eq178626 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq178598
  have eq541432 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq178626
       grind)
    | exact superpose eq178626 eq16
    | exact resolve eq16 eq178626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178626
  have eq541581 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq541432
       have i₂ := eq13626
       grind)
    | exact superpose eq13626 eq541432
    | exact resolve eq541432 eq13626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13626 eq541432
  have eq541582 : y = (M.op x x) := by grind
  clear eq541581
  have eq617463 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq444 x
       have i₂ := eq541582
       grind)
    | exact superpose eq541582 eq444
    | exact resolve eq444 eq541582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq617501 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq192 x x
       have i₂ := eq541582
       grind)
    | exact superpose eq541582 eq192
    | exact resolve eq192 eq541582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq617644 : x = y := by
    first
    | (have i₁ := eq617501
       have i₂ := eq17644 x
       grind)
    | exact superpose eq17644 eq617501
    | exact resolve eq617501 eq17644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17644 eq617501
  have eq617668 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq617463
       have r₂ := eq16
       grind)
    | exact resolve eq617463 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617463
  have eq617741 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq617668
       have i₂ := eq617644
       grind)
    | exact superpose eq617644 eq617668
    | exact resolve eq617668 eq617644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617668
  have eq694156 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq617644
       grind)
    | exact superpose eq617644 eq16
    | exact resolve eq16 eq617644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694174 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq694156
       have i₂ := eq541582
       grind)
    | exact superpose eq541582 eq694156
    | exact resolve eq694156 eq541582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541582 eq694156
  have eq694177 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq694174
       have i₂ := eq617741
       grind)
    | exact superpose eq617741 eq694174
    | exact resolve eq694174 eq617741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617741 eq694174
  have eq694179 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq694177
       have i₂ := eq617644
       grind)
    | exact superpose eq617644 eq694177
    | exact resolve eq694177 eq617644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617644 eq694177
  have eq694180 : False := by grind
  exact eq694180

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_y_x_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  clear eq18
  have eq25 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq33 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq43 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq37
    | exact resolve eq37 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq87 : ∀ X0 : G, (τ (σ X0)) = (k (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (τ (M.op (σ (σ X0)) (σ (σ X0)))) X0
       have i₂ := eq43 (σ X0)
       grind)
    | exact superpose eq43 eq23
    | exact resolve eq23 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq88 : ∀ X0 : G, (k (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq87
    | exact resolve eq87 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) = (M.op (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X1 (M.op (M.op X2 X0) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq95 (M.op X1 (M.op (M.op X2 X0) X0)) X1 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq95
    | exact resolve eq95 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq14 (σ (M.op (τ X0) (τ X0))) X0
       grind)
    | exact superpose eq14 eq33
    | (have j1 := eq14 (σ (M.op (τ X0) (τ X0))) X0
       grind)
    | exact resolve eq33 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq480 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq3033 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq13 (σ (M.op (τ X0) (τ X0))) X0
       have i₂ := eq499 X0
       grind)
    | exact superpose eq499 eq13
    | (have j0 := eq13 (σ (M.op (τ X0) (τ X0))) X0
       have j1 := eq499 X0
       grind)
    | (have r₁ := eq13 (σ (M.op (τ X0) (τ X0))) X0
       have r₂ := eq499 X0
       grind)
    | exact resolve eq13 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3035 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq3033 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3033
  have eq3036 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq3035 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035
  have eq3038 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq3036 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq3036
    | (have j0 := eq3036 X0
       grind)
    | exact resolve eq3036 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3036
  have eq3040 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq3038 eq499
    | (have j0 := eq499 X0
       have j1 := eq3038 X0
       grind)
    | exact resolve eq499 eq3038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq3107 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq3038 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3108 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0)))) = (M.op X4 (M.op X4 (M.op (M.op X2 (M.op (M.op X3 X0) X0)) (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq94 (M.op X1 (M.op (M.op X2 X0) X0)) X1 X2 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq94
    | exact resolve eq94 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3109 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X4 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))))) = (M.op X5 (M.op X5 (M.op (M.op X4 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X4 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))))))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq94 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0)))) X1 X2 X1
       have i₂ := eq94 X0 X1 X2 X3
       grind)
    | exact superpose eq94 eq94
    | exact resolve eq94 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3114 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq94
    | exact resolve eq94 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3128 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq3114 X1 x X3
       have i₂ := eq3114 X1 x X0
       grind)
    | exact superpose eq3114 eq3114
    | exact resolve eq3114 eq3114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3131 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) (M.op (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3114 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) X3 x
       have i₂ := eq94 X2 x X0 X1
       grind)
    | exact superpose eq94 eq3114
    | exact resolve eq3114 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3135 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq3114 X1 x X0
       grind)
    | exact superpose eq3114 eq9
    | exact resolve eq9 eq3114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3141 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 X0 (M.op X2 X0) X2
       have i₂ := eq3114 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq3114 eq95
    | exact resolve eq95 eq3114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3149 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3141 X0 X1 X2
       have i₂ := eq95 X0 X0 X1
       grind)
    | exact superpose eq95 eq3141
    | exact resolve eq3141 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3141
  have eq3159 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq3135 X0 (M.op X0 X0)
       have i₂ := eq3135 X0 X0
       grind)
    | exact superpose eq3135 eq3135
    | exact resolve eq3135 eq3135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3166 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 (M.op X0 (M.op X0 X1)) X1 X1
       have i₂ := eq3135 X0 X1
       grind)
    | exact superpose eq3135 eq95
    | exact resolve eq95 eq3135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3167 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) = (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3114 (M.op X1 (M.op X1 X0)) X0 X2
       have i₂ := eq3135 X1 X0
       grind)
    | exact superpose eq3135 eq3114
    | exact resolve eq3114 eq3135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3114
  have eq3169 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) = (M.op (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3167 X0 X1 X2
       have i₂ := eq3135 X1 X0
       grind)
    | exact superpose eq3135 eq3167
    | exact resolve eq3167 eq3135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167
  have eq3170 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3166 X1 X0 X2
       have i₂ := eq3135 X0 X1
       grind)
    | exact superpose eq3135 eq3166
    | exact resolve eq3166 eq3135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3166
  have eq3177 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq3159 X0
       grind)
    | exact superpose eq3159 eq9
    | exact resolve eq9 eq3159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3210 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3128 X1 (M.op X1 (M.op X0 X0)) X2
       have i₂ := eq3177 X0 X1
       grind)
    | exact superpose eq3177 eq3128
    | exact resolve eq3128 eq3177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3211 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3128 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq3135 X1 X0
       grind)
    | exact superpose eq3135 eq3128
    | exact resolve eq3128 eq3135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3213 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X2 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3128 X2 (M.op X2 X1) X3
       have i₂ := eq3128 X2 X1 X0
       grind)
    | (have i₁ := eq3128 X2 (M.op X2 X1) X3
       have i₂ := eq3128 X0 X1 X2
       grind)
    | exact superpose eq3128 eq3128
    | exact resolve eq3128 eq3128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3259 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X2 X1) (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3135 X2 (M.op X2 X1)
       have i₂ := eq3128 X2 X1 X0
       grind)
    | (have i₁ := eq3135 X2 (M.op X2 X1)
       have i₂ := eq3128 X0 X1 X2
       grind)
    | exact superpose eq3128 eq3135
    | exact resolve eq3135 eq3128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3296 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3149 X0 X1 X0
       have i₂ := eq3159 X0
       grind)
    | exact superpose eq3159 eq3149
    | exact resolve eq3149 eq3159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3149 eq3159
  have eq3356 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94 X0 X1 X2 X1
       have i₂ := eq3296 X0 X1
       grind)
    | exact superpose eq3296 eq94
    | exact resolve eq94 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq3357 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1 X1
       have i₂ := eq3296 X0 X1
       grind)
    | exact superpose eq3296 eq95
    | exact resolve eq95 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq3371 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3357 X1 X1
       have i₂ := eq3128 X1 X1 X0
       grind)
    | (have i₁ := eq3357 X1 X1
       have i₂ := eq3128 X0 X1 X1
       grind)
    | exact superpose eq3128 eq3357
    | exact resolve eq3357 eq3128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3387 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 (M.op X3 (M.op X2 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3170 (M.op X2 X1) X3 X2
       have i₂ := eq3128 X2 X1 X0
       grind)
    | (have i₁ := eq3170 (M.op X2 X1) X3 X2
       have i₂ := eq3128 X0 X1 X2
       grind)
    | exact superpose eq3128 eq3170
    | exact resolve eq3170 eq3128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3170
  have eq3506 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3211 (M.op X1 X0) X1 X1
       have i₂ := eq3211 X0 X1 X1
       grind)
    | exact superpose eq3211 eq3211
    | exact resolve eq3211 eq3211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3507 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3211 X2 X1 X1
       have i₂ := eq3128 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq3211 X2 X1 X1
       have i₂ := eq3128 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq3128 eq3211
    | exact resolve eq3211 eq3128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4209 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = (M.op (M.op X1 (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3135 x (M.op X1 (M.op X0 (M.op X1 X1)))
       have i₂ := eq3356 X1 x X0
       grind)
    | exact superpose eq3356 eq3135
    | exact resolve eq3135 eq3356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4239 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4209 X0 X1
       have i₂ := eq3296 (M.op X0 (M.op X1 X1)) X1
       grind)
    | exact superpose eq3296 eq4209
    | exact resolve eq4209 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4209
  have eq4270 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4239 X0 X1
       have i₂ := eq3506 (M.op X1 X1) X0
       grind)
    | exact superpose eq3506 eq4239
    | exact resolve eq4239 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4239
  have eq4291 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4270 X0 X1
       have i₂ := eq3506 X1 X1
       grind)
    | exact superpose eq3506 eq4270
    | exact resolve eq4270 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4270
  have eq4401 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) = (M.op (M.op X1 (M.op X0 (M.op X1 X1))) (M.op X1 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3210 (M.op X1 (M.op X0 (M.op X1 X1))) (M.op X1 (M.op X0 (M.op X1 X1))) X2
       have i₂ := eq3356 X1 (M.op X1 (M.op X0 (M.op X1 X1))) X0
       grind)
    | exact superpose eq3356 eq3210
    | exact resolve eq3210 eq3356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4434 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3356 X1 X1 X0
       have i₂ := eq3210 X1 X0 X1
       grind)
    | exact superpose eq3210 eq3356
    | exact resolve eq3356 eq3210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4497 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) = (M.op X1 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4401 X0 X1 X2
       have i₂ := eq3506 (M.op X0 (M.op X1 X1)) X1
       grind)
    | exact superpose eq3506 eq4401
    | exact resolve eq4401 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4401
  have eq4522 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) = (M.op X1 (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4497 X0 X1 X2
       have i₂ := eq3506 (M.op X1 X1) X0
       grind)
    | exact superpose eq3506 eq4497
    | exact resolve eq4497 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4497
  have eq4532 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) = (M.op X1 (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4522 X0 X1 X2
       have i₂ := eq3506 X1 X1
       grind)
    | exact superpose eq3506 eq4522
    | exact resolve eq4522 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4522
  have eq4533 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4532 X0 X1 x
       have i₂ := eq3210 X1 X0 x
       grind)
    | exact superpose eq3210 eq4532
    | exact resolve eq4532 eq3210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4532
  have eq4590 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3507 X1 X0 X1
       have i₂ := eq4434 X0 X1
       grind)
    | (have i₁ := eq3507 X0 X1 X1
       have i₂ := eq4434 X0 X1
       grind)
    | exact superpose eq4434 eq3507
    | exact resolve eq3507 eq4434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3507
  have eq5457 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq460 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq460
    | (have j0 := eq460 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq460 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5459 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq5464 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq460 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq460
    | (have j0 := eq460 (σ X0) (σ X1)
       grind)
    | exact resolve eq460 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5500 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq460 X1 X0
       grind)
    | exact superpose eq460 eq10
    | (have j1 := eq460 X1 X0
       grind)
    | exact resolve eq10 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq5565 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq5459 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5459
  have eq5935 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4533 X2 X1
       have i₂ := eq3128 X1 X1 X0
       grind)
    | (have i₁ := eq4533 X2 X1
       have i₂ := eq3128 X0 X1 X1
       grind)
    | exact superpose eq3128 eq4533
    | exact resolve eq4533 eq3128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3128 eq4533
  have eq10050 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq5565 X0
       grind)
    | exact superpose eq5565 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (σ X0)
       have j1 := eq5565 X0
       grind)
    | (have r₁ := eq13 (σ (M.op X0 X0)) (σ X0)
       have r₂ := eq5565 X0
       grind)
    | exact resolve eq13 eq5565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10083 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq10050 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10050
  have eq10084 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq10083 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10083
  have eq10095 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10084 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq10084
    | (have j0 := eq10084 X0
       grind)
    | exact resolve eq10084 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10084
  have eq10103 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq10095
  have eq10131 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq3040 X0
       grind)
    | exact superpose eq3040 eq10
    | (have j1 := eq3040 X0
       grind)
    | exact resolve eq10 eq3040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3040
  have eq10207 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = (M.op X2 (M.op X4 (M.op X4 (M.op X2 (M.op X3 (M.op X3 X0)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3213 X4 (M.op X2 (M.op X3 (M.op X3 X0))) X2 X1
       have i₂ := eq3211 X0 X3 X2
       grind)
    | exact superpose eq3211 eq3213
    | exact resolve eq3213 eq3211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10724 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X4 (M.op X4 (M.op X2 (M.op X3 (M.op X3 X0)))))) = X0 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq10207 X0 x X2 X3 X4
       have i₂ := eq3177 X0 x
       grind)
    | exact superpose eq3177 eq10207
    | exact resolve eq10207 eq3177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10207
  have eq10936 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3259 X0 (M.op X0 X0) X1
       have i₂ := eq3135 X0 X0
       grind)
    | exact superpose eq3135 eq3259
    | exact resolve eq3259 eq3135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11840 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X0)) (M.op X2 (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4291 X2 (M.op X1 (M.op X1 X0))
       have i₂ := eq3211 X0 X1 (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq3211 eq4291
    | exact resolve eq4291 eq3211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11881 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 (M.op X0 (M.op X1 X1))))) = (M.op X3 (M.op X1 (M.op X0 (M.op X1 (M.op X1 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3213 X1 (M.op X0 (M.op X1 X1)) X3 X2
       have i₂ := eq4291 X0 X1
       grind)
    | (have i₁ := eq3213 X0 (M.op X1 (M.op X1 X1)) X2 X3
       have i₂ := eq4291 X0 X1
       grind)
    | exact superpose eq4291 eq3213
    | exact resolve eq3213 eq4291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11911 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3259 X0 X0 X1
       have i₂ := eq4291 X1 X0
       grind)
    | (have i₁ := eq3259 X1 X1 X1
       have i₂ := eq4291 X1 X1
       grind)
    | exact superpose eq4291 eq3259
    | exact resolve eq3259 eq4291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4291
  have eq12088 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op X2 (M.op X2 (M.op X3 (M.op X0 (M.op X1 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11881 X0 X1 X2 X3
       have i₂ := eq5935 X1 X1 X0
       grind)
    | exact superpose eq5935 eq11881
    | exact resolve eq11881 eq5935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11881
  have eq12119 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X0)) (M.op X2 (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11840 X0 X1 X2
       have i₂ := eq3506 (M.op X1 X0) X1
       grind)
    | exact superpose eq3506 eq11840
    | exact resolve eq11840 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11840
  have eq12205 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X0)) (M.op X2 (M.op X1 (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12119 X0 X1 X2
       have i₂ := eq3506 X0 X1
       grind)
    | exact superpose eq3506 eq12119
    | exact resolve eq12119 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12119
  have eq12262 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12205 X0 X1 X2
       have i₂ := eq3177 X0 X1
       grind)
    | exact superpose eq3177 eq12205
    | exact resolve eq12205 eq3177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12205
  have eq12360 : ∀ X0 X1 X2 : G, (M.op (τ X0) (M.op X2 (M.op X2 (τ X0)))) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3213 X2 (τ X0) (τ X0) X1
       have i₂ := eq10131 X0
       grind)
    | exact superpose eq10131 eq3213
    | (have j1 := eq10131 X0
       grind)
    | exact resolve eq3213 eq10131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12362 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (M.op (τ X0) (M.op X1 (M.op X1 (τ X0))))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3259 X0 (τ X0) (τ X0)
       have i₂ := eq10131 X0
       grind)
    | exact superpose eq10131 eq3259
    | (have j1 := eq10131 X0
       grind)
    | exact resolve eq3259 eq10131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12389 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12362 X0 x
       have i₂ := eq3135 x (τ X0)
       grind)
    | exact superpose eq3135 eq12362
    | (have j0 := eq12362 X0 x
       grind)
    | exact resolve eq12362 eq3135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12362
  have eq12390 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12360 X0 X1 x
       have i₂ := eq3135 x (τ X0)
       grind)
    | exact superpose eq3135 eq12360
    | (have j0 := eq12360 X0 X1 x
       grind)
    | exact resolve eq12360 eq3135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12360
  have eq23092 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X3 (M.op X3 (M.op X1 (M.op X1 X2)))) (M.op X0 (M.op (M.op X1 (M.op X1 X2)) (M.op X1 (M.op X1 X2)))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10724 X2 X0 X1 (M.op X3 (M.op X3 (M.op X1 (M.op X1 X2))))
       have i₂ := eq12262 (M.op X1 (M.op X1 X2)) X3 X0
       grind)
    | exact superpose eq12262 eq10724
    | exact resolve eq10724 eq12262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10724 eq12262
  have eq23266 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X3 (M.op X3 (M.op X1 (M.op X1 X2)))) (M.op X0 (M.op X1 (M.op (M.op X1 X2) (M.op X1 X2)))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23092 X0 X1 X2 X3
       have i₂ := eq3506 (M.op X1 X2) X1
       grind)
    | exact superpose eq3506 eq23092
    | exact resolve eq23092 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23092
  have eq23486 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X3 (M.op X3 (M.op X1 (M.op X1 X2)))) (M.op X0 (M.op X1 (M.op X1 (M.op X2 X2)))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23266 X0 X1 X2 X3
       have i₂ := eq3506 X2 X1
       grind)
    | exact superpose eq3506 eq23266
    | exact resolve eq23266 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23266
  have eq23635 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X3 (M.op X3 (M.op X1 (M.op X1 X2)))) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23486 X0 X1 X2 X3
       have i₂ := eq3177 X2 X1
       grind)
    | exact superpose eq3177 eq23486
    | exact resolve eq23486 eq3177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23486
  have eq29061 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = (M.op (M.op X3 (M.op X0 (M.op X1 (M.op X0 X0)))) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq125 X0 X1 X1 X3
       have i₂ := eq3296 X0 X1
       grind)
    | exact superpose eq3296 eq125
    | exact resolve eq125 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq37781 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0)))) = (M.op X4 (M.op X4 (M.op (M.op X2 (M.op X0 X0)) (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0))))))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq3108 X0 X1 X2 X1 X4
       have i₂ := eq3296 X0 X1
       grind)
    | exact superpose eq3296 eq3108
    | exact resolve eq3108 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3108
  have eq39436 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (M.op X0 X0))) (M.op (M.op X0 (M.op X1 (M.op X0 X0))) (M.op X0 (M.op X1 (M.op X0 X0))))) = (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X0 (M.op X1 (M.op X0 X0))) (M.op X0 (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3356 (M.op X0 (M.op X1 (M.op X0 X0))) (M.op X0 (M.op X1 (M.op X0 X0))) (M.op X1 (M.op X0 X0))
       have i₂ := eq37781 X0 (M.op X0 (M.op X1 (M.op X0 X0))) X1 (M.op X0 (M.op X1 (M.op X0 X0)))
       grind)
    | exact superpose eq37781 eq3356
    | exact resolve eq3356 eq37781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3356
  have eq39698 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))))) = (M.op (M.op X0 (M.op X1 (M.op X0 X0))) (M.op X0 (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq39436 X1 X1
       have i₂ := eq3506 (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact superpose eq3506 eq39436
    | exact resolve eq39436 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39436
  have eq39936 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (M.op X0 X0))) (M.op X0 (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))))) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq39698 X0 X1
       have i₂ := eq3506 (M.op X0 X0) X1
       grind)
    | exact superpose eq3506 eq39698
    | exact resolve eq39698 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39698
  have eq40096 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X1 (M.op X0 (M.op (M.op X0 X0) X0))))) = (M.op (M.op X0 (M.op X1 (M.op X0 X0))) (M.op X0 (M.op X1 (M.op X0 (M.op (M.op X0 X0) X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq39936 X1 X1
       have i₂ := eq4434 (M.op X1 X1) X1
       grind)
    | exact superpose eq4434 eq39936
    | exact resolve eq39936 eq4434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39936
  have eq40211 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (M.op X0 X0))) (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0))))) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq40096 X0 X1
       have i₂ := eq3296 X0 X0
       grind)
    | exact superpose eq3296 eq40096
    | exact resolve eq40096 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40096
  have eq40309 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X1 X0)) = (M.op (M.op X0 (M.op X1 (M.op X0 X0))) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq40211 X0 x
       have i₂ := eq5935 X0 X0 x
       grind)
    | exact superpose eq5935 eq40211
    | exact resolve eq40211 eq5935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40211
  have eq40403 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 (M.op X1 (M.op X0 X0))) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq40309 X0 X1
       have i₂ := eq10936 X0 X1
       grind)
    | exact superpose eq10936 eq40309
    | exact resolve eq40309 eq10936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40309
  have eq42146 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq5464 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42147 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq42146 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42146
  have eq43601 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 (M.op X1 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12390 (σ X0) X1
       have i₂ := eq5500 X0 X0
       grind)
    | exact superpose eq5500 eq12390
    | (have j0 := eq12390 (σ X0) X1
       have j1 := eq5500 X0 X0
       grind)
    | exact resolve eq12390 eq5500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12390
  have eq43776 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 (M.op X1 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq43601 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43601
  have eq43846 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (k X0 X0))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq43776 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq43776
    | (have j0 := eq43776 X0 X1
       grind)
    | exact resolve eq43776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43776
  have eq44601 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq10103 eq5565
    | (have j0 := eq5565 X0
       have j1 := eq10103 X0
       grind)
    | exact resolve eq5565 eq10103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5565
  have eq44622 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5500 X0 X0
       have i₂ := eq10103 X0
       grind)
    | exact superpose eq10103 eq5500
    | (have j1 := eq10103 X0
       grind)
    | exact resolve eq5500 eq10103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5500
  have eq44624 : ∀ X0 : G, (σ (M.op (σ X0) (σ X0))) = (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (σ (M.op (σ X0) (σ X0))) ∨ (σ (σ X0)) = (σ (M.op (σ X0) (σ X0))) ∨ (σ (σ X0)) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5464 x x
       have i₂ := eq10103 (σ x)
       grind)
    | exact superpose eq10103 eq5464
    | (have j1 := eq10103 (σ X0)
       grind)
    | exact resolve eq5464 eq10103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5464 eq10103
  have eq44739 : ∀ X0 : G, (σ (M.op (σ X0) (σ X0))) = (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq44624 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44624
  have eq44740 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq44622 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44622
  have eq44762 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq44740 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq44740
    | (have j0 := eq44740 X0
       grind)
    | exact resolve eq44740 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44740
  have eq44766 : ∀ X0 : G, (σ (M.op (σ X0) (σ X0))) = (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq44739 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44739
  have eq44800 : ∀ X0 : G, (k (σ (τ X0)) X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq44762 (τ X0)
       grind)
    | exact superpose eq44762 eq33
    | (have j1 := eq44762 (τ X0)
       grind)
    | exact resolve eq33 eq44762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq44808 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq44762 X0
       grind)
    | exact superpose eq44762 eq10
    | (have j1 := eq44762 X0
       grind)
    | exact resolve eq10 eq44762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44762
  have eq44934 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq44808 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44808
    | (have j0 := eq44808 X0
       grind)
    | exact resolve eq44808 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44808
  have eq44942 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq44800 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq44800
    | (have j0 := eq44800 X0
       grind)
    | exact resolve eq44800 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44800
  have eq44960 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq44942 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq44942
    | (have j0 := eq44942 X0
       grind)
    | exact resolve eq44942 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44942
  have eq45127 : ∀ X0 : G, (M.op X0 X0) = (σ (τ (k X0 X0))) ∨ (σ (τ (k X0 X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3038 X0
       have i₂ := eq44960 X0
       grind)
    | exact superpose eq44960 eq3038
    | (have j1 := eq44960 X0
       grind)
    | exact resolve eq3038 eq44960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45264 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ (k X0 X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq45127 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq45127
    | (have j0 := eq45127 X0
       grind)
    | exact resolve eq45127 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45127
  have eq45271 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq45264 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq45264
    | (have j0 := eq45264 X0
       grind)
    | exact resolve eq45264 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45264
  have eq45272 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq45271 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45271
  have eq45290 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq45272 eq44960
    | (have j0 := eq44960 X0
       have j1 := eq45272 X0
       grind)
    | exact resolve eq44960 eq45272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44960
  have eq45344 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq45272 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45988 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3296 (τ X0) (τ X0)
       have i₂ := eq45290 X0
       grind)
    | exact superpose eq45290 eq3296
    | (have j1 := eq45290 X0
       grind)
    | exact resolve eq3296 eq45290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48435 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X1))) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 X1) (M.op (M.op X1 (M.op X0 (M.op X1 X1))) (M.op (M.op X0 X1) (M.op X0 X1)))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40403 (M.op X0 X1) (M.op X1 (M.op X0 (M.op X1 X1)))
       have i₂ := eq40403 X1 X0
       grind)
    | exact superpose eq40403 eq40403
    | exact resolve eq40403 eq40403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48719 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X1 (M.op X0 (M.op X1 X1))) (M.op X0 X1))) = (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op (M.op X1 (M.op X0 (M.op X1 X1))) (M.op X0 X1)))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq48435 X0 X1
       have i₂ := eq4434 (M.op X1 (M.op X0 (M.op X1 X1))) (M.op X0 X1)
       grind)
    | exact superpose eq4434 eq48435
    | exact resolve eq48435 eq4434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48435
  have eq48957 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1)))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq48719 X1 X0
       have i₂ := eq40403 X0 X1
       grind)
    | exact superpose eq40403 eq48719
    | exact resolve eq48719 eq40403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40403 eq48719
  have eq49146 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq48957 X0 X1
       have i₂ := eq3371 (M.op X0 X1) (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq3371 eq48957
    | exact resolve eq48957 eq3371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48957
  have eq49290 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq49146 X0 X1
       have i₂ := eq3506 (M.op X1 X1) X0
       grind)
    | exact superpose eq3506 eq49146
    | exact resolve eq49146 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49146
  have eq49364 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq49290 X0 X1
       have i₂ := eq4434 (M.op X1 X1) X1
       grind)
    | exact superpose eq4434 eq49290
    | exact resolve eq49290 eq4434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49290
  have eq49409 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq49364 X0 X1
       have i₂ := eq3296 X1 X1
       grind)
    | exact superpose eq3296 eq49364
    | exact resolve eq49364 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49364
  have eq51192 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq44601 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44601
  have eq51217 : ∀ X0 : G, (σ (M.op (σ X0) (σ X0))) = (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq44766 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44766
  have eq51327 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5457 x y
       grind)
    | exact superpose eq5457 eq16
    | (have j1 := eq5457 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq5457 x y
       grind)
    | exact resolve eq16 eq5457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5457
  have eq51508 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq51327
  have eq51892 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))))) = (M.op (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3169 (M.op X0 (M.op X1 X1)) (M.op X0 X1) X2
       have i₂ := eq49409 X0 X1
       grind)
    | exact superpose eq49409 eq3169
    | exact resolve eq3169 eq49409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3169 eq49409
  have eq52013 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X2 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51892 X2 X0 X2
       have i₂ := eq3259 X0 X0 X2
       grind)
    | exact superpose eq3259 eq51892
    | exact resolve eq51892 eq3259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51892
  have eq73270 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = (M.op (M.op X3 (M.op X3 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3387 X3 (M.op X1 (M.op X2 X2)) X0 x
       have i₂ := eq12088 X1 X2 x X0
       grind)
    | exact superpose eq12088 eq3387
    | exact resolve eq3387 eq12088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387 eq12088
  have eq73524 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73270 X0 X1 X2 x
       have i₂ := eq3210 X2 X1 x
       grind)
    | exact superpose eq3210 eq73270
    | exact resolve eq73270 eq3210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73270
  have eq110918 : ∀ X0 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X0 (M.op X2 X2)) (M.op X4 (M.op X2 (M.op X0 (M.op X2 X2)))))) = (M.op X5 (M.op X5 (M.op (M.op X4 (M.op X2 (M.op X0 (M.op X2 X2)))) (M.op X3 (M.op (M.op X0 (M.op X2 X2)) (M.op X4 (M.op X2 (M.op X0 (M.op X2 X2))))))))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq3109 X0 x X0 X3 X4 X5
       have i₂ := eq3296 X0 x
       grind)
    | exact superpose eq3296 eq3109
    | exact resolve eq3109 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3109
  have eq111226 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq110918 X2 X1 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) X0 X3
       have i₂ := eq37781 X1 X0 X2 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1))))
       grind)
    | exact superpose eq37781 eq110918
    | exact resolve eq110918 eq37781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37781
  have eq111459 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))))))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) = (M.op X4 (M.op X4 (M.op (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52013 (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) X4
       have i₂ := eq110918 X1 X2 X0 X3 (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))))))
       grind)
    | exact superpose eq110918 eq52013
    | exact resolve eq52013 eq110918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111817 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) = (M.op (M.op (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))))))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq111459 X0 X1 X2 X3 x
       have i₂ := eq3177 (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) x
       grind)
    | exact superpose eq3177 eq111459
    | exact resolve eq111459 eq3177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111459
  have eq111989 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq111226 X0 X1 X2 X3
       have i₂ := eq4434 (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1))))
       grind)
    | exact superpose eq4434 eq111226
    | exact resolve eq111226 eq4434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111226
  have eq112309 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) = (M.op (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))))))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq111817 X0 X1 X2 X3
       have i₂ := eq3506 (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))))) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))
       grind)
    | exact superpose eq3506 eq111817
    | exact resolve eq111817 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111817
  have eq112433 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X1 (M.op X2 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq111989 X0 X1 X2 X3
       have i₂ := eq3506 (M.op X1 (M.op X2 (M.op X1 X1))) X0
       grind)
    | exact superpose eq3506 eq111989
    | exact resolve eq111989 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111989
  have eq112665 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) = (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq112309 X0 X1 X2 X3
       have i₂ := eq3357 (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))))) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))
       grind)
    | exact superpose eq3357 eq112309
    | exact resolve eq112309 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357 eq112309
  have eq112738 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op (M.op X2 (M.op X1 X1)) (M.op X2 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq112433 X0 X1 X2 X3
       have i₂ := eq3506 (M.op X2 (M.op X1 X1)) X1
       grind)
    | exact superpose eq3506 eq112433
    | exact resolve eq112433 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112433
  have eq112931 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) = (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))) (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq112665 X0 X1 X2 X3
       have i₂ := eq3506 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))) X0
       grind)
    | exact superpose eq3506 eq112665
    | exact resolve eq112665 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112665
  have eq113000 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq112738 X0 X1 X2 X3
       have i₂ := eq3506 (M.op X1 X1) X2
       grind)
    | exact superpose eq3506 eq112738
    | exact resolve eq112738 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112738
  have eq113133 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) = (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq112931 X0 X1 X2 X3
       have i₂ := eq3506 (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X1 (M.op X2 X2))
       grind)
    | exact superpose eq3506 eq112931
    | exact resolve eq112931 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112931
  have eq113201 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 (M.op (M.op X1 X1) X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113000 X0 X1 X2 X3
       have i₂ := eq4434 (M.op X1 X1) X1
       grind)
    | exact superpose eq4434 eq113000
    | exact resolve eq113000 eq4434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113000
  have eq113311 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) = (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op (M.op X2 (M.op X1 (M.op X2 X2))) (M.op X2 (M.op X1 (M.op X2 X2))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113133 X0 X1 X2 X3
       have i₂ := eq3506 (M.op X2 (M.op X1 (M.op X2 X2))) X3
       grind)
    | exact superpose eq3506 eq113133
    | exact resolve eq113133 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113133
  have eq113379 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113201 X0 X1 X2 X3
       have i₂ := eq3296 X1 X1
       grind)
    | exact superpose eq3296 eq113201
    | exact resolve eq113201 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113201
  have eq113481 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) = (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op (M.op X1 (M.op X2 X2)) (M.op X1 (M.op X2 X2))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113311 X0 X1 X2 X3
       have i₂ := eq3506 (M.op X1 (M.op X2 X2)) X2
       grind)
    | exact superpose eq3506 eq113311
    | exact resolve eq113311 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113311
  have eq113548 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113379 X0 X1 X2 X3
       have i₂ := eq5935 X1 X1 X2
       grind)
    | exact superpose eq5935 eq113379
    | exact resolve eq113379 eq5935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113379
  have eq113639 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) = (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op (M.op X2 X2) (M.op X2 X2))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113481 X0 X1 X2 X3
       have i₂ := eq3506 (M.op X2 X2) X1
       grind)
    | exact superpose eq3506 eq113481
    | exact resolve eq113481 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113481
  have eq113785 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) = (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 (M.op (M.op X2 X2) X2))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113639 X0 X1 X2 X3
       have i₂ := eq4434 (M.op X2 X2) X2
       grind)
    | exact superpose eq4434 eq113639
    | exact resolve eq113639 eq4434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113639
  have eq113884 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) = (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 (M.op X2 X2))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113785 X0 X1 X2 X3
       have i₂ := eq3296 X2 X2
       grind)
    | exact superpose eq3296 eq113785
    | exact resolve eq113785 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113785
  have eq113925 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X1 X2)))) = (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113884 X0 X1 X2 X3
       have i₂ := eq5935 X2 X2 X1
       grind)
    | exact superpose eq5935 eq113884
    | exact resolve eq113884 eq5935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113884
  have eq114017 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X1 X2)))) = (M.op (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2)))) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 (M.op X2 (M.op X1 (M.op X2 X2))))))) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq113925 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113925
  have eq117220 : ∀ X0 : G, (σ (σ (τ X0))) ≠ (σ (k (σ (τ X0)) X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq42147 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq42147
    | (have j0 := eq42147 (τ X0)
       grind)
    | exact resolve eq42147 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42147
  have eq117232 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq117220 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq117220
    | (have j0 := eq117220 X0
       grind)
    | exact resolve eq117220 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117220
  have eq117239 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq117232 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq117232
    | (have j0 := eq117232 X0
       grind)
    | exact resolve eq117232 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117232
  have eq117249 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq117239 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq117239
    | (have j0 := eq117239 (τ X0)
       grind)
    | exact resolve eq117239 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117239
  have eq117261 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq117249 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq117249
    | (have j0 := eq117249 X0
       grind)
    | exact resolve eq117249 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117249
  have eq117268 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq117261 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq117261
    | (have j0 := eq117261 X0
       grind)
    | exact resolve eq117261 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117261
  have eq117276 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq117268 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq117268
    | (have j0 := eq117268 (τ X0)
       grind)
    | exact resolve eq117268 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq126703 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X1 (M.op X1 (M.op X2 (M.op X2 (k X0 X0))))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23635 (M.op X1 (M.op X1 (M.op X2 (M.op X2 (k X0 X0))))) X2 (k X0 X0) X1
       have i₂ := eq43846 X0 (M.op X1 (M.op X1 (M.op X2 (M.op X2 (k X0 X0)))))
       grind)
    | exact superpose eq43846 eq23635
    | (have j1 := eq43846 X0 X1
       grind)
    | exact resolve eq23635 eq43846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23635
  have eq126708 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) X0) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq43846 eq126703
    | (have j0 := eq126703 X0 X1 x
       have j1 := eq43846 X0 X1
       grind)
    | exact resolve eq126703 eq43846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43846 eq126703
  have eq126821 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq126708 X0 x
       have i₂ := eq3371 x X0
       grind)
    | exact superpose eq3371 eq126708
    | (have j0 := eq126708 X0 x
       grind)
    | exact resolve eq126708 eq3371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3371 eq126708
  have eq126901 : ∀ X0 : G, (k (τ (τ (σ (σ X0)))) X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq126821 (σ X0)
       grind)
    | exact superpose eq126821 eq88
    | (have j1 := eq126821 (σ X0)
       grind)
    | exact resolve eq88 eq126821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq126821
  have eq127165 : ∀ X0 : G, (k (τ (σ X0)) X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq126901 X0
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq126901
    | (have j0 := eq126901 X0
       grind)
    | exact resolve eq126901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126901
  have eq127217 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq127165 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq127165
    | (have j0 := eq127165 X0
       grind)
    | exact resolve eq127165 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127165
  have eq127239 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq127217 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq127217
    | (have j0 := eq127217 X0
       grind)
    | exact resolve eq127217 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127217
  have eq127247 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq45272 eq127239
    | (have j0 := eq127239 X0
       have j1 := eq45272 X0
       grind)
    | exact resolve eq127239 eq45272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45272 eq127239
  have eq127355 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3296 (σ X0) (σ X0)
       have i₂ := eq127247 X0
       grind)
    | exact superpose eq127247 eq3296
    | (have j1 := eq127247 X0
       grind)
    | exact resolve eq3296 eq127247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127247
  have eq151182 : ∀ X0 : G, (σ (k (σ (τ X0)) X0)) = (σ (M.op (σ (τ X0)) (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (σ (M.op (σ (τ X0)) (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq51217 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq51217
    | (have j0 := eq51217 (τ X0)
       grind)
    | exact resolve eq51217 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51217
  have eq151340 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (σ (σ (τ X0))) = (σ (M.op (σ (τ X0)) (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq151182 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq151182
    | (have j0 := eq151182 X0
       grind)
    | exact resolve eq151182 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151182
  have eq151348 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq151340 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq151340
    | (have j0 := eq151340 X0
       grind)
    | exact resolve eq151340 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151340
  have eq151368 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq151348 (τ X0)
       grind)
    | exact superpose eq151348 eq19
    | (have j1 := eq151348 (τ X0)
       grind)
    | exact resolve eq19 eq151348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq151516 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (τ X0)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq151368 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq151368
    | (have j0 := eq151368 X0
       grind)
    | exact resolve eq151368 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151368
  have eq151539 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq151516 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq151516
    | (have j0 := eq151516 X0
       grind)
    | exact resolve eq151516 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151516
  have eq151552 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq3038 eq151539
    | (have j0 := eq151539 X0
       have j1 := eq3038 X0
       grind)
    | exact resolve eq151539 eq3038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3038 eq151539
  have eq151591 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq151552 X0
       grind)
    | exact superpose eq151552 eq10
    | (have j1 := eq151552 X0
       grind)
    | exact resolve eq10 eq151552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151552
  have eq151734 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | exact superpose eq151591 eq117276
    | (have j0 := eq117276 X0
       have j1 := eq151591 X0
       grind)
    | exact resolve eq117276 eq151591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117276
  have eq151737 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq151591 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq151591
    | (have j0 := eq151591 (σ X0)
       grind)
    | exact resolve eq151591 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151770 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3107 (τ X0)
       have i₂ := eq151591 X0
       grind)
    | exact superpose eq151591 eq3107
    | (have j0 := eq3107 (τ X0)
       have j1 := eq151591 X0
       grind)
    | (have r₁ := eq3107 (τ X0)
       have r₂ := eq151591 X0
       grind)
    | exact resolve eq3107 eq151591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151591
  have eq151945 : ∀ X0 : G, (τ X0) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq151770 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151770
  have eq152051 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq151737 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq151737
    | (have j0 := eq151737 X0
       grind)
    | exact resolve eq151737 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151737
  have eq152104 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq44934 eq152051
    | (have j0 := eq152051 X0
       have j1 := eq44934 X0
       grind)
    | exact resolve eq152051 eq44934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44934 eq152051
  have eq152325 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3296 (σ X0) (σ X0)
       have i₂ := eq152104 X0
       grind)
    | exact superpose eq152104 eq3296
    | (have j1 := eq152104 X0
       grind)
    | exact resolve eq3296 eq152104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152104
  have eq174245 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X1))) (M.op X1 (M.op X0 (M.op X1 X1)))) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3211 (M.op X1 (M.op X0 (M.op X1 X1))) X2 X2
       have i₂ := eq113548 X2 X1 X0 X2
       grind)
    | exact superpose eq113548 eq3211
    | exact resolve eq3211 eq113548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113548
  have eq175753 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq174245 X0 X1 X2
       have i₂ := eq3506 (M.op X0 (M.op X1 X1)) X1
       grind)
    | exact superpose eq3506 eq174245
    | exact resolve eq174245 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174245
  have eq176932 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175753 X0 X1 X2
       have i₂ := eq3506 (M.op X1 X1) X0
       grind)
    | exact superpose eq3506 eq175753
    | exact resolve eq175753 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175753
  have eq177839 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1)))) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176932 X0 X1 X2
       have i₂ := eq4434 (M.op X1 X1) X1
       grind)
    | exact superpose eq4434 eq176932
    | exact resolve eq176932 eq4434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176932
  have eq178588 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X1 X1)))) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177839 X0 X1 X2
       have i₂ := eq3296 X1 X1
       grind)
    | exact superpose eq3296 eq177839
    | exact resolve eq177839 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177839
  have eq179166 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178588 X0 X1 X2
       have i₂ := eq5935 X1 X1 X0
       grind)
    | exact superpose eq5935 eq178588
    | exact resolve eq178588 eq5935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178588
  have eq182759 : x = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq43 x
       have i₂ := eq51508
       grind)
    | exact superpose eq51508 eq43
    | exact resolve eq43 eq51508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51508
  have eq183012 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq182759
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq182759
    | exact resolve eq182759 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182759
  have eq183032 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq183012
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq183012 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183012
  have eq183033 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq183032
  have eq251400 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (M.op (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) (M.op X2 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X0 (M.op (M.op X1 X2) X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3131 X0 X1 X2 X3
       have i₂ := eq73524 (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) X2 (M.op X0 (M.op (M.op X1 X2) X2))
       grind)
    | exact superpose eq73524 eq3131
    | exact resolve eq3131 eq73524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3131
  have eq251401 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (M.op (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) (M.op X2 (M.op X0 (M.op (M.op (M.op X1 X2) X2) (M.op (M.op X1 X2) X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq251400 X0 X1 X2 X3
       have i₂ := eq3506 (M.op (M.op X1 X2) X2) X0
       grind)
    | exact superpose eq3506 eq251400
    | exact resolve eq251400 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251400
  have eq251402 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (M.op (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X2 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq251401 X0 X1 X2 X3
       have i₂ := eq3506 X2 (M.op X1 X2)
       grind)
    | exact superpose eq3506 eq251401
    | exact resolve eq251401 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251401
  have eq251403 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (M.op (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) (M.op X2 (M.op X0 (M.op X2 (M.op (M.op X1 X2) X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq251402 X0 X1 X2 X3
       have i₂ := eq4434 (M.op X1 X2) X2
       grind)
    | exact superpose eq4434 eq251402
    | exact resolve eq251402 eq4434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251402
  have eq251404 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X2 X2)) = (M.op (M.op X3 (M.op X2 (M.op X0 (M.op X2 X2)))) (M.op X2 (M.op X0 (M.op X2 (M.op X2 X2))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq251403 X0 x X0 X3
       have i₂ := eq3296 X0 x
       grind)
    | exact superpose eq3296 eq251403
    | exact resolve eq251403 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251403
  have eq251405 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X2 X2)) = (M.op (M.op X3 (M.op X2 (M.op X0 (M.op X2 X2)))) (M.op X0 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq251404 X0 X2 X3
       have i₂ := eq5935 X2 X2 X0
       grind)
    | exact superpose eq5935 eq251404
    | exact resolve eq251404 eq5935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251404
  have eq251480 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op (M.op X3 (M.op (M.op X0 X2) (M.op X0 (M.op X1 (M.op X1 X2))))) (M.op (M.op X0 X2) (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq251405 (M.op X2 X1) (M.op X2 X1) X3
       have i₂ := eq3213 X0 X1 X2 (M.op X2 X1)
       grind)
    | exact superpose eq3213 eq251405
    | exact resolve eq251405 eq3213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3213 eq251405
  have eq252786 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op (M.op X0 X2) (M.op (M.op X3 (M.op (M.op X0 X2) (M.op X0 (M.op X1 (M.op X1 X2))))) (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq251480 X0 X1 X2 X3
       have i₂ := eq4434 (M.op X3 (M.op (M.op X0 X2) (M.op X0 (M.op X1 (M.op X1 X2))))) (M.op X0 X2)
       grind)
    | exact superpose eq4434 eq251480
    | exact resolve eq251480 eq4434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251480
  have eq253321 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op (M.op X3 (M.op (M.op X0 X2) (M.op X0 (M.op X1 (M.op X1 X2))))) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq252786 X0 X1 X2 X3
       have i₂ := eq73524 (M.op X3 (M.op (M.op X0 X2) (M.op X0 (M.op X1 (M.op X1 X2))))) X0 X2
       grind)
    | exact superpose eq73524 eq252786
    | exact resolve eq252786 eq73524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73524 eq252786
  have eq253717 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op (M.op X3 (M.op X0 X2)) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq253321 X0 X1 X2 X3
       have i₂ := eq3259 X1 X2 X0
       grind)
    | exact superpose eq3259 eq253321
    | exact resolve eq253321 eq3259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253321
  have eq313332 : ∀ X0 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X0 (M.op X2 X2)) (M.op X4 (M.op X2 (M.op X0 (M.op X2 X2)))))) = (M.op X5 (M.op X5 (M.op X3 (M.op (M.op X0 (M.op X2 X2)) (M.op X4 (M.op X0 X2)))))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq110918 X0 X2 X3 X4 X5
       have i₂ := eq114017 X3 X0 X2 X4
       grind)
    | exact superpose eq114017 eq110918
    | exact resolve eq110918 eq114017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110918 eq114017
  have eq320893 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X2 X1)))))) = (M.op (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X2 X1))))))) (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X1 (M.op X2 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29061 (M.op X2 (M.op X0 (M.op X2 X2))) (M.op X0 (M.op X2 X2)) X3
       have i₂ := eq313332 X0 X2 (M.op X2 (M.op X0 (M.op X2 X2))) (M.op X2 (M.op X0 (M.op X2 X2))) x
       grind)
    | exact superpose eq313332 eq29061
    | exact resolve eq29061 eq313332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29061
  have eq322736 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X2 X1)))))) = (M.op (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X2 X1))))))) (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op (M.op X2 (M.op X1 X1)) (M.op X2 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq320893 X0 X1 X2 X3
       have i₂ := eq3506 (M.op X2 (M.op X1 X1)) X1
       grind)
    | exact superpose eq3506 eq320893
    | exact resolve eq320893 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320893
  have eq324600 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X2 X1)))))) = (M.op (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X2 X1))))))) (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq322736 X0 X1 X2 X3
       have i₂ := eq3506 (M.op X1 X1) X2
       grind)
    | exact superpose eq3506 eq322736
    | exact resolve eq322736 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3506 eq322736
  have eq326215 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X2 X1)))))) = (M.op (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X2 X1))))))) (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 (M.op (M.op X1 X1) X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq324600 X0 X1 X2 X3
       have i₂ := eq4434 (M.op X1 X1) X1
       grind)
    | exact superpose eq4434 eq324600
    | exact resolve eq324600 eq4434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4434 eq324600
  have eq327585 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X2 X1)))))) = (M.op (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X2 X1))))))) (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq326215 X0 X1 X2 X3
       have i₂ := eq3296 X1 X1
       grind)
    | exact superpose eq3296 eq326215
    | exact resolve eq326215 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326215
  have eq328798 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X2 X1)))))) = (M.op (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X2 X1))))))) (M.op (M.op X2 (M.op X1 X1)) (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq327585 X0 X1 X2 X3
       have i₂ := eq5935 X1 X1 X2
       grind)
    | exact superpose eq5935 eq327585
    | exact resolve eq327585 eq5935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5935 eq327585
  have eq329818 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X2 X1)))))) = (M.op (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X2 X1))))))) (M.op X2 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq328798 X0 X1 X2 X3
       have i₂ := eq10936 X1 X2
       grind)
    | exact superpose eq10936 eq328798
    | exact resolve eq328798 eq10936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328798
  have eq330647 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op X2 X1))) = (M.op (M.op X3 (M.op X0 (M.op X0 (M.op X2 X1)))) (M.op X2 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq329818 X0 X1 X0 X3
       have i₂ := eq179166 X0 X1 (M.op X1 (M.op X0 (M.op X1 X1)))
       grind)
    | exact superpose eq179166 eq329818
    | exact resolve eq329818 eq179166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179166 eq329818
  have eq348714 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X1 X2))))) (M.op (M.op X1 (M.op X2 X2)) (M.op (M.op X1 X2) (M.op X2 (M.op X1 (M.op X2 X2)))))) = (M.op X4 (M.op X4 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq313332 X1 X2 (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X1 X2))))) (M.op X1 X2) X4
       have i₂ := eq330647 X0 (M.op X1 X2) (M.op X1 (M.op X2 X2)) X3
       grind)
    | exact superpose eq330647 eq313332
    | exact resolve eq313332 eq330647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313332 eq330647
  have eq349046 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op X2 X2))))) (M.op (M.op X1 (M.op X2 X2)) (M.op (M.op X1 X2) (M.op X2 (M.op X1 (M.op X2 X2)))))) = (M.op X4 (M.op X4 (M.op X0 (M.op X0 (M.op X1 (M.op X2 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq348714 X0 X1 X0 X3 X4
       have i₂ := eq10936 X0 X1
       grind)
    | exact superpose eq10936 eq348714
    | exact resolve eq348714 eq10936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348714
  have eq350024 : ∀ X1 X2 X3 X4 : G, (M.op X4 (M.op X4 (M.op X1 X2))) = (M.op (M.op X3 (M.op X1 X2)) (M.op (M.op X1 (M.op X2 X2)) (M.op (M.op X1 X2) (M.op X2 (M.op X1 (M.op X2 X2)))))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq349046 X2 X1 x X3 X4
       have i₂ := eq3210 x X1 X2
       grind)
    | exact superpose eq3210 eq349046
    | exact resolve eq349046 eq3210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3210 eq349046
  have eq350822 : ∀ X1 X2 X3 X4 : G, (M.op X4 (M.op X4 (M.op X1 X2))) = (M.op (M.op X3 (M.op X1 X2)) (M.op (M.op X1 (M.op X2 X2)) (M.op X1 X2))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq350024 X1 X2 X3 X4
       have i₂ := eq11911 X2 X1
       grind)
    | exact superpose eq11911 eq350024
    | exact resolve eq350024 eq11911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350024
  have eq351395 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X1 X2)) (M.op X1 (M.op X2 X2))) = (M.op X4 (M.op X4 (M.op X1 X2))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq350822 X1 X2 X3 X4
       have i₂ := eq10936 X2 X1
       grind)
    | exact superpose eq10936 eq350822
    | exact resolve eq350822 eq10936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10936 eq350822
  have eq488846 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (M.op X0 (σ y))))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq3259 X0 (σ y) (σ x)
       have i₂ := eq183033
       grind)
    | exact superpose eq183033 eq3259
    | exact resolve eq3259 eq183033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3259
  have eq489058 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq488846 x
       have i₂ := eq3211 (σ y) x (σ x)
       grind)
    | exact superpose eq3211 eq488846
    | exact resolve eq488846 eq3211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3211 eq488846
  have eq513739 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12389 (σ y)
       have i₂ := eq489058
       grind)
    | exact superpose eq489058 eq12389
    | exact resolve eq12389 eq489058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12389
  have eq513751 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45988 (σ y)
       have i₂ := eq489058
       grind)
    | exact superpose eq489058 eq45988
    | (have j0 := eq45988 (σ y)
       grind)
    | exact resolve eq45988 eq489058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45988 eq489058
  have eq514040 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq513751
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq513751
    | exact resolve eq513751 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513751
  have eq514044 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq513739
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq513739
    | exact resolve eq513739 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513739
  have eq514081 : x = (M.op x y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq514040
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq514040
    | exact resolve eq514040 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514040
  have eq514082 : x = (M.op x y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq514081
  have eq514085 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq514044
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq514044
    | exact resolve eq514044 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514044
  have eq514086 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq514085
  have eq514091 : (σ y) = (σ (k y y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq514082
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq514082
    | exact resolve eq514082 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514082
  have eq514098 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq514086 eq183033
    | exact resolve eq183033 eq514086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183033
  have eq514861 : (σ x) = (σ (k y y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq514086 eq514091
    | exact resolve eq514091 eq514086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514091
  have eq516868 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq151348 y
       have i₂ := eq514861
       grind)
    | exact superpose eq514861 eq151348
    | (have j0 := eq151348 y
       grind)
    | exact resolve eq151348 eq514861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151348 eq514861
  have eq517156 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq514086 eq516868
    | exact resolve eq516868 eq514086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514086 eq516868
  have eq517157 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq517156
  have eq528565 : (τ (σ x)) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq517157
       grind)
    | exact superpose eq517157 eq10
    | exact resolve eq10 eq517157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517157
  have eq528857 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq528565
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq528565
    | exact resolve eq528565 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528565
  have eq588851 : x = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq43 x
       have i₂ := eq514098
       grind)
    | exact superpose eq514098 eq43
    | exact resolve eq43 eq514098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq588922 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq151734 (σ x)
       have i₂ := eq514098
       grind)
    | exact superpose eq514098 eq151734
    | (have j0 := eq151734 (σ x)
       grind)
    | exact resolve eq151734 eq514098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151734 eq514098
  have eq589132 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq588922
  have eq589273 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq589132
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq589132
    | exact resolve eq589132 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589132
  have eq589303 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq588851
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq588851
    | exact resolve eq588851 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588851
  have eq589426 : x ≠ y ∨ x = (σ (M.op (τ x) (τ x))) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq3107 x
       have i₂ := eq589303
       grind)
    | exact superpose eq589303 eq3107
    | (have j0 := eq3107 x
       grind)
    | exact resolve eq3107 eq589303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589768 : x ≠ y ∨ x = (σ (τ (M.op x x))) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | exact superpose eq45290 eq589426
    | (have j1 := eq45290 x
       grind)
    | exact resolve eq589426 eq45290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45290 eq589426
  have eq589801 : x = (M.op x x) ∨ x ≠ y ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq589768
       have i₂ := eq11 (M.op x x)
       grind)
    | exact superpose eq11 eq589768
    | exact resolve eq589768 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589768
  have eq589806 : x ≠ y ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq117268 x
       grind)
    | (have r₁ := eq589801
       have r₂ := eq117268 x
       grind)
    | exact resolve eq589801 eq117268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589801
  have eq590303 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq127355 x
       have i₂ := eq589273
       grind)
    | exact superpose eq589273 eq127355
    | (have j0 := eq127355 x
       grind)
    | exact resolve eq127355 eq589273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590307 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq152325 x
       have i₂ := eq589273
       grind)
    | exact superpose eq589273 eq152325
    | (have j0 := eq152325 x
       grind)
    | exact resolve eq152325 eq589273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589273
  have eq590586 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq590307
       have r₂ := eq589806
       grind)
    | exact resolve eq590307 eq589806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590307
  have eq590588 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq45344 x
       grind)
    | (have r₁ := eq590303
       have r₂ := eq45344 x
       grind)
    | exact resolve eq590303 eq45344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45344 eq590303
  have eq607905 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq590588
  have eq692233 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq151945 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq151945
    | (have j0 := eq151945 (σ X0)
       grind)
    | exact resolve eq151945 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151945
  have eq692575 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq692233 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq692233
    | (have j0 := eq692233 X0
       grind)
    | exact resolve eq692233 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692233
  have eq749408 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ x))))) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq11911 (σ x) (σ y)
       have i₂ := eq607905
       grind)
    | exact superpose eq607905 eq11911
    | exact resolve eq11911 eq607905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607905
  have eq749600 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq749408
       have i₂ := eq4590 (σ y) (σ x)
       grind)
    | exact superpose eq4590 eq749408
    | exact resolve eq749408 eq4590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749408
  have eq750498 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq692575 X0
       grind)
    | exact superpose eq692575 eq10
    | (have j1 := eq692575 X0
       grind)
    | exact resolve eq10 eq692575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692575
  have eq754746 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ x))))) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11911 (σ x) (σ y)
       have i₂ := eq590586
       grind)
    | exact superpose eq590586 eq11911
    | exact resolve eq11911 eq590586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590586
  have eq754939 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq754746
       have i₂ := eq4590 (σ y) (σ x)
       grind)
    | exact superpose eq4590 eq754746
    | exact resolve eq754746 eq4590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754746
  have eq780350 : (k x x) = (τ (σ y)) ∨ x = (σ (M.op (τ x) (τ x))) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq750498 x
       have i₂ := eq754939
       grind)
    | exact superpose eq754939 eq750498
    | (have j0 := eq750498 x
       grind)
    | exact resolve eq750498 eq754939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750498 eq754939
  have eq780808 : (k x x) = (τ (σ y)) ∨ x = (σ (M.op (τ x) (τ x))) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq3107 x
       grind)
    | (have r₁ := eq780350
       have r₂ := eq3107 x
       grind)
    | exact resolve eq780350 eq3107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3107 eq780350
  have eq780868 : x = (σ (M.op (τ x) (τ x))) ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq780808
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq780808
    | exact resolve eq780808 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780808
  have eq797567 : x = (σ (τ (M.op x x))) ∨ y = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq780868
       have i₂ := eq10131 x
       grind)
    | exact superpose eq10131 eq780868
    | (have j1 := eq10131 x
       grind)
    | exact resolve eq780868 eq10131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10131 eq780868
  have eq797885 : x = (M.op x x) ∨ y = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq797567
       have i₂ := eq11 (M.op x x)
       grind)
    | exact superpose eq11 eq797567
    | exact resolve eq797567 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797567
  have eq797886 : y = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq797885
  have eq964064 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 (M.op X1 X1)))) = (M.op (σ (M.op X0 (M.op X0 (M.op X1 X1)))) (σ (M.op X1 (M.op X1 X1)))) ∨ (M.op X0 (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq152325 (M.op x (M.op x x))
       have i₂ := eq351395 x x x x
       grind)
    | exact superpose eq351395 eq152325
    | exact resolve eq152325 eq351395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351395
  have eq966236 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X1 (M.op X1 X1)))) ∨ (M.op X0 (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq964064 X1 X0
       have i₂ := eq3177 X0 X1
       grind)
    | exact superpose eq3177 eq964064
    | (have j0 := eq964064 X0 X1
       grind)
    | exact resolve eq964064 eq3177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964064
  have eq968385 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = X1 ∨ (σ X1) = (M.op (σ X1) (σ (M.op X1 (M.op X1 X1)))) := by
    intro X1
    first
    | (have i₁ := eq966236 x X1
       have i₂ := eq3177 X1 x
       grind)
    | exact superpose eq3177 eq966236
    | (have j0 := eq966236 x X1
       grind)
    | exact resolve eq966236 eq3177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966236
  have eq1005503 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq968385 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968385
  have eq1504070 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X1 X0)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X1 X0)))) (σ (M.op X0 (M.op X0 X0)))) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq127355 (M.op x (M.op x x))
       have i₂ := eq253717 x X1 x x
       grind)
    | exact superpose eq253717 eq127355
    | (have j0 := eq127355 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq127355 eq253717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127355 eq253717
  have eq1504767 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1504070 x X0
       have i₂ := eq3135 X0 x
       grind)
    | exact superpose eq3135 eq1504070
    | (have j0 := eq1504070 X0 x
       grind)
    | exact resolve eq1504070 eq3135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3135 eq1504070
  have eq1507560 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1005503 eq1504767
    | (have j0 := eq1504767 X0
       have j1 := eq1005503 X0
       grind)
    | exact resolve eq1504767 eq1005503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005503 eq1504767
  have eq1524620 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (M.op (σ X0) (M.op (σ X0) (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52013 (σ X0) (σ (M.op X0 (M.op X0 X0))) x
       have i₂ := eq1507560 X0
       grind)
    | exact superpose eq1507560 eq52013
    | (have j1 := eq1507560 X0
       grind)
    | exact resolve eq52013 eq1507560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52013 eq1507560
  have eq1524800 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (σ (M.op X0 (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1524620 X0 X1
       have i₂ := eq3177 (σ (M.op X0 (M.op X0 X0))) (σ X0)
       grind)
    | exact superpose eq3177 eq1524620
    | (have j0 := eq1524620 X0 X1
       grind)
    | exact resolve eq1524620 eq3177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3177 eq1524620
  have eq1527188 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op x x))) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1524800 x (σ x)
       have i₂ := eq749600
       grind)
    | exact superpose eq749600 eq1524800
    | (have j0 := eq1524800 x x
       grind)
    | exact resolve eq1524800 eq749600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749600 eq1524800
  have eq1528384 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op x x))) ∨ x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq1527188
  have eq1529107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq589303 eq1528384
    | exact resolve eq1528384 eq589303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589303 eq1528384
  have eq1529627 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1529107
       have r₂ := eq16
       grind)
    | exact resolve eq1529107 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529107
  have eq1530138 : x = y ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1529627 eq797886
    | exact resolve eq797886 eq1529627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797886
  have eq1530197 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1530138
       have r₂ := eq589806
       grind)
    | exact resolve eq1530138 eq589806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589806 eq1530138
  have eq1530226 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1530197 eq528857
    | exact resolve eq528857 eq1530197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528857 eq1530197
  have eq1571996 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3296 y y
       have i₂ := eq1530226
       grind)
    | exact superpose eq1530226 eq3296
    | exact resolve eq3296 eq1530226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296 eq1530226
  have eq1572234 : x = (M.op x y) ∨ x = y := by grind
  clear eq1571996
  have eq1572886 : x = (M.op x (M.op y (M.op x (M.op y y)))) ∨ x = y := by
    first
    | (have i₁ := eq11911 y x
       have i₂ := eq1572234
       grind)
    | exact superpose eq1572234 eq11911
    | exact resolve eq11911 eq1572234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11911
  have eq1573097 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1572886
       have i₂ := eq4590 x y
       grind)
    | exact superpose eq4590 eq1572886
    | exact resolve eq1572886 eq4590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4590 eq1572886
  have eq1606663 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq152325 y
       have i₂ := eq1573097
       grind)
    | exact superpose eq1573097 eq152325
    | exact resolve eq152325 eq1573097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152325 eq1573097
  have eq1607024 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1606663
  have eq1620877 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1607024
       grind)
    | exact superpose eq1607024 eq16
    | exact resolve eq16 eq1607024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607024
  have eq1621237 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq1572234 eq1620877
    | exact resolve eq1620877 eq1572234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572234 eq1620877
  have eq1621238 : x = y := by grind
  clear eq1621237
  have eq1621312 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1621238
       grind)
    | exact superpose eq1621238 eq16
    | exact resolve eq16 eq1621238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1621313 : x = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1529627
       have i₂ := eq1621238
       grind)
    | exact superpose eq1621238 eq1529627
    | exact resolve eq1529627 eq1621238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529627 eq1621238
  have eq1621331 : x = (M.op x x) := by
    first
    | (have j1 := eq117268 x
       grind)
    | (have r₁ := eq1621313
       have r₂ := eq117268 x
       grind)
    | exact resolve eq1621313 eq117268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117268 eq1621313
  have eq1621346 : x = (M.op x x) := by grind
  clear eq1621331
  have eq1621349 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1621312
       have i₂ := eq1621346
       grind)
    | exact superpose eq1621346 eq1621312
    | exact resolve eq1621312 eq1621346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621312
  have eq1621390 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq51192 x
       have i₂ := eq1621346
       grind)
    | exact superpose eq1621346 eq51192
    | (have j0 := eq51192 x
       grind)
    | exact resolve eq51192 eq1621346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51192 eq1621346
  have eq1621745 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1621390
  have eq1621992 : False := by grind
  exact eq1621992

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq41 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq41 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) (σ X1)
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq42 (τ X0)
       grind)
    | exact superpose eq42 eq18
    | exact resolve eq18 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq82
    | exact resolve eq82 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq82
  have eq94 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq114 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq140 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 y x
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 y x
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq153 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq9
    | exact resolve eq9 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq140
       have i₂ := eq94 y
       grind)
    | exact superpose eq94 eq140
    | exact resolve eq140 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq465 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq464
       have i₂ := eq94 x
       grind)
    | exact superpose eq94 eq464
    | exact resolve eq464 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq502 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq465
       have i₂ := eq55 y x
       grind)
    | exact superpose eq55 eq465
    | (have j1 := eq55 x y
       grind)
    | exact resolve eq465 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq465
  have eq503 : (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq502
  have eq548 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op X1 (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq114 (σ X0) (σ X0) X1
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq114
    | exact resolve eq114 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1694 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (M.op X0 (M.op X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq153 X1 (σ X1)
       have i₂ := eq548 X1 X0
       grind)
    | exact superpose eq548 eq153
    | exact resolve eq153 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq548
  have eq1817 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1694 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1694
    | exact resolve eq1694 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694
  have eq1894 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1817 (M.op X0 X0) X0
       have i₂ := eq1817 X0 X0
       grind)
    | exact superpose eq1817 eq1817
    | exact resolve eq1817 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817
  have eq2018 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq1894 X0
       grind)
    | exact superpose eq1894 eq9
    | exact resolve eq9 eq1894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894
  have eq2193 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2018 (σ X0) X1
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq2018
    | exact resolve eq2018 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2195 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x x))) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq2018 y X0
       have i₂ := eq503
       grind)
    | exact superpose eq503 eq2018
    | exact resolve eq2018 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq2245 : x = y ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2195 x
       have i₂ := eq2018 x x
       grind)
    | exact superpose eq2018 eq2195
    | exact resolve eq2195 eq2018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018 eq2195
  have eq5051 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2245
       grind)
    | exact superpose eq2245 eq16
    | exact resolve eq16 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245
  have eq5052 : (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5051
       have r₂ := eq94 x
       grind)
    | exact resolve eq5051 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5051
  have eq5054 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq2193 y X0
       have i₂ := eq5052
       grind)
    | exact superpose eq5052 eq2193
    | exact resolve eq2193 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5052
  have eq5102 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq5054 x
       have i₂ := eq2193 x x
       grind)
    | exact superpose eq2193 eq5054
    | exact resolve eq5054 eq2193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193 eq5054
  have eq5106 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5102
       grind)
    | exact superpose eq5102 eq10
    | exact resolve eq10 eq5102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5102
  have eq5156 : x = y := by
    first
    | (have i₁ := eq5106
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5106
    | exact resolve eq5106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5106
  have eq5330 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5156
       grind)
    | exact superpose eq5156 eq16
    | exact resolve eq16 eq5156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5156
  have eq5331 : False := by grind
  exact eq5331
