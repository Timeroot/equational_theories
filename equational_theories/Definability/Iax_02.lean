import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation895`: `x = y ◇ ((x ◇ z) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation895 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law895 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law895.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X2) (M.op X1 X2))) = X0 := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X0 X3) (M.op X2 X3))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X1 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq8 X0 X2 X3
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
  clear eq16
  have eq27 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 X1 x
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 X1
       have i₂ := eq66 X1 (M.op X0 X1)
       grind)
    | exact superpose eq66 eq8
    | exact resolve eq8 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X1 (M.op X0 X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq82
    | exact resolve eq82 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (M.op X1 X1)
       have i₂ := eq66 X1 X0
       grind)
    | exact superpose eq66 eq82
    | exact resolve eq82 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq173 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 (M.op X1 X1)
       have i₂ := eq66 X1 X0
       grind)
    | exact superpose eq66 eq114
    | exact resolve eq114 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X0 X1) X0) ∨ (k (M.op X2 X1) X2) = (M.op (M.op X2 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X2 (M.op X0 X1) (M.op X2 X1)
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq29
    | (have j0 := eq29 X2 X1 (M.op X2 X1)
       grind)
    | exact resolve eq29 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq250 : ∀ X1 X2 : G, (M.op X2 X1) = X1 ∨ (k (M.op X2 X1) X2) = (M.op (M.op X2 X1) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq209 x X1 X2
       have i₂ := eq114 x X1
       grind)
    | exact superpose eq114 eq209
    | (have j0 := eq209 x X1 X2
       grind)
    | exact resolve eq209 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq262 : ∀ X1 X2 : G, (k (M.op X2 X1) X2) = X1 ∨ (M.op X2 X1) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq250 X1 X2
       have i₂ := eq114 X2 X1
       grind)
    | exact superpose eq114 eq250
    | (have j0 := eq250 X1 X2
       grind)
    | exact resolve eq250 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq288 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 X1
       have i₂ := eq115 (M.op X0 X1) X1
       grind)
    | exact superpose eq115 eq8
    | exact resolve eq8 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X1 (M.op X1 X0)
       have i₂ := eq288 X1 X0
       grind)
    | exact superpose eq288 eq114
    | exact resolve eq114 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq288
  have eq541 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq14
    | (have j1 := eq31 x y
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq810 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (M.op X1 X1) X0
       have i₂ := eq115 X0 X1
       grind)
    | exact superpose eq115 eq47
    | (have j0 := eq47 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq47 (M.op X1 X1) X0
       have r₂ := eq115 X0 X1
       grind)
    | exact resolve eq47 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq814 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq810 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq841 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X1 X1) X0
       have i₂ := eq814 (σ X0) X1
       grind)
    | exact superpose eq814 eq24
    | exact resolve eq24 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq814 (τ X0) X1
       grind)
    | exact superpose eq814 eq17
    | exact resolve eq17 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq843 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq842 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq842
    | exact resolve eq842 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq844 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq841 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq841
    | exact resolve eq841 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq846 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq262 (M.op X0 X0) X1
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq262
    | exact resolve eq262 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq900 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 X1))
       have i₂ := eq843 (τ X0) X1
       grind)
    | exact superpose eq843 eq17
    | exact resolve eq17 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq900 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq900
    | exact resolve eq900 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq1103 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (τ (M.op X1 X1)) X0
       have i₂ := eq844 (σ X0) X1
       grind)
    | exact superpose eq844 eq24
    | exact resolve eq24 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1106 : ∀ X0 X1 : G, (k (τ (τ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1103 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1103
    | exact resolve eq1103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1234 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (σ (M.op X1 X1)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq901 (τ X0) X1
       grind)
    | exact superpose eq901 eq17
    | exact resolve eq17 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq1235 : ∀ X0 X1 : G, (k (σ (σ (σ (M.op X1 X1)))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1234 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1234
    | exact resolve eq1234 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq2942 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq541
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq541
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq541 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq2943 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2942
  have eq103855 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq843 (σ (M.op X1 X1)) X1
       have i₂ := eq846 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq846 eq843
    | (have j1 := eq846 (σ (M.op X1 X1)) X0
       grind)
    | exact resolve eq843 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq103856 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) ∨ (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq901 (σ (σ (M.op X1 X1))) X1
       have i₂ := eq846 (σ (σ (M.op X1 X1))) X0
       grind)
    | exact superpose eq846 eq901
    | (have j1 := eq846 (σ (σ (M.op X1 X1))) X0
       grind)
    | exact resolve eq901 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq103857 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (σ (M.op X1 X1)))) ∨ (M.op X0 X0) = (σ (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1235 (σ (σ (σ (M.op X1 X1)))) X1
       have i₂ := eq846 (σ (σ (σ (M.op X1 X1)))) X0
       grind)
    | exact superpose eq846 eq1235
    | (have j1 := eq846 (σ (σ (σ (M.op X1 X1)))) X0
       grind)
    | exact resolve eq1235 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq103862 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq844 (τ (M.op X1 X1)) X1
       have i₂ := eq846 (τ (M.op X1 X1)) X0
       grind)
    | exact superpose eq846 eq844
    | (have j1 := eq846 (τ (M.op X1 X1)) X0
       grind)
    | exact resolve eq844 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq103863 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (τ (M.op X1 X1))) ∨ (M.op X0 X0) = (τ (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1106 (τ (τ (M.op X1 X1))) X1
       have i₂ := eq846 (τ (τ (M.op X1 X1))) X0
       grind)
    | exact superpose eq846 eq1106
    | (have j1 := eq846 (τ (τ (M.op X1 X1))) X0
       grind)
    | exact resolve eq1106 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq103866 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq846 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq103869 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq103863 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103863
  have eq103870 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq103862 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103862
  have eq103872 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq103857 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103857
  have eq103873 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq103856 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103856
  have eq103874 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq103855 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103855
  have eq108069 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq103870 x X2
       have i₂ := eq103874 x X0
       grind)
    | exact superpose eq103874 eq103870
    | exact resolve eq103870 eq103874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119818 : ∀ X0 X2 : G, (τ (M.op X2 X2)) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq108069 x X2
       have i₂ := eq103873 x X0
       grind)
    | exact superpose eq103873 eq108069
    | exact resolve eq108069 eq103873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103873 eq108069
  have eq125263 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq103866 X1 X0
       have i₂ := eq27 X0 X0
       grind)
    | exact superpose eq27 eq103866
    | (have j0 := eq103866 X1 X0
       have j1 := eq27 X0 X0
       grind)
    | (have r₁ := eq103866 X0 X0
       have r₂ := eq27 X0 X0
       grind)
    | exact resolve eq103866 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq125285 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq125263 X0 X1
       have j1 := eq103866 X1 X0
       grind)
    | (have r₁ := eq125263 X1 X1
       have r₂ := eq103866 X1 X1
       grind)
    | (have r₁ := eq125263 (M.op X0 X0) X1
       have r₂ := eq103866 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq125263 (k (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq103866 X0 (M.op X1 X1)
       grind)
    | exact resolve eq125263 eq103866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103866 eq125263
  have eq125646 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq125285 X1 X2
       have i₂ := eq173 X1 X0
       grind)
    | (have i₁ := eq125285 X1 X2
       have i₂ := eq173 X0 X1
       grind)
    | exact superpose eq173 eq125285
    | (have j0 := eq125285 X1 X2
       grind)
    | (have r₁ := eq125285 (M.op X1 X1) X1
       have r₂ := eq173 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq125285 (M.op X0 X0) X1
       have r₂ := eq173 X0 (M.op X0 X0)
       grind)
    | exact resolve eq125285 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq125285
  have eq128311 : ∀ X0 X2 X3 : G, (σ (σ (σ (M.op X0 X0)))) ≠ X2 ∨ (M.op X3 X3) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq125646 x X2 X3
       have i₂ := eq103872 x X0
       grind)
    | exact superpose eq103872 eq125646
    | (have j0 := eq125646 X0 X2 X3
       grind)
    | (have r₁ := eq125646 X0 (σ (σ (σ (M.op x x)))) X2
       have r₂ := eq103872 X0 x
       grind)
    | exact resolve eq125646 eq103872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103872 eq125646
  have eq147851 : ∀ X0 : G, (σ (σ (σ (M.op X0 X0)))) = (τ (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq119818 X0 (σ x)
       have i₂ := eq2943
       grind)
    | exact superpose eq2943 eq119818
    | exact resolve eq119818 eq2943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2943 eq119818
  have eq147954 : ∀ X0 : G, y = (σ (σ (σ (M.op X0 X0)))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq147851 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq147851
    | exact resolve eq147851 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147851
  have eq147995 : y = (M.op x x) := by
    first
    | (have j1 := eq128311 x y x
       grind)
    | (have r₁ := eq147954 x
       have r₂ := eq128311 x y x
       grind)
    | exact resolve eq147954 eq128311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128311 eq147954
  have eq148007 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq66 x X0
       have i₂ := eq147995
       grind)
    | exact superpose eq147995 eq66
    | exact resolve eq66 eq147995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq148009 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq115 X0 x
       have i₂ := eq147995
       grind)
    | exact superpose eq147995 eq115
    | exact resolve eq115 eq147995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq148027 : ∀ X0 : G, (M.op X0 X0) = (τ (τ y)) := by
    intro X0
    first
    | (have i₁ := eq103869 X0 x
       have i₂ := eq147995
       grind)
    | exact superpose eq147995 eq103869
    | exact resolve eq103869 eq147995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103869
  have eq148028 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq103870 X0 x
       have i₂ := eq147995
       grind)
    | exact superpose eq147995 eq103870
    | exact resolve eq103870 eq147995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103870
  have eq148032 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq103874 X0 x
       have i₂ := eq147995
       grind)
    | exact superpose eq147995 eq103874
    | exact resolve eq103874 eq147995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103874 eq147995
  have eq148240 : (σ y) = (τ y) := by
    first
    | (have i₁ := eq148028 x
       have i₂ := eq148032 x
       grind)
    | exact superpose eq148032 eq148028
    | exact resolve eq148028 eq148032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148028
  have eq148241 : (σ y) = (τ (τ y)) := by
    first
    | (have i₁ := eq148027 x
       have i₂ := eq148032 x
       grind)
    | exact superpose eq148032 eq148027
    | exact resolve eq148027 eq148032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148027 eq148032
  have eq148289 : (σ y) = (τ (σ y)) := by
    first
    | (have i₁ := eq148241
       have i₂ := eq148240
       grind)
    | exact superpose eq148240 eq148241
    | exact resolve eq148241 eq148240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148240 eq148241
  have eq148321 : y = (σ y) := by
    first
    | (have i₁ := eq148289
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq148289
    | exact resolve eq148289 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148289
  have eq148502 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq148321
       grind)
    | exact superpose eq148321 eq14
    | exact resolve eq14 eq148321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148321
  have eq148546 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq148502
       have i₂ := eq498 (σ x) y
       grind)
    | (have i₁ := eq148502
       have i₂ := eq498 y (σ x)
       grind)
    | exact superpose eq498 eq148502
    | exact resolve eq148502 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq148502
  have eq148561 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq148546
       have i₂ := eq148009 (σ x)
       grind)
    | exact superpose eq148009 eq148546
    | exact resolve eq148546 eq148009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148009 eq148546
  have eq148568 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq148561
       have i₂ := eq148007 x
       grind)
    | exact superpose eq148007 eq148561
    | exact resolve eq148561 eq148007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148007 eq148561
  have eq148569 : False := by grind
  exact eq148569

/-- `Equation978`: `x = y ◇ ((z ◇ z) ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation978 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law978 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law978.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) (M.op X0 X1))) = X0 := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) (M.op (M.op X3 X3) X0)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X1) (M.op X0 X2)) X3
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op X1 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X2 X2) (M.op X0 (M.op X1 X1)) X1
       have i₂ := eq8 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 x x X0
       have i₂ := eq19 x x X1
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = X3 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X2 X3
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = (k X2 (M.op (M.op X0 (M.op X1 X1)) X0)) := by
    intro X0 X1 X2
    grind
  have eq56 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 (M.op X1 X1)
       have i₂ := eq19 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq60 : ∀ X0 X2 : G, (M.op X0 X0) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq53 x X0 X2
       have i₂ := eq56 X0 x
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq62 : ∀ X0 X2 X3 : G, (M.op X0 X0) = X3 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq51 X0 x X2 X3
       have i₂ := eq56 x X0
       grind)
    | exact superpose eq56 eq51
    | (have j0 := eq51 X0 x X2 X3
       grind)
    | exact resolve eq51 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq124 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 (M.op X1 X1) X2
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq8
    | exact resolve eq8 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq142 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X5 X5) (M.op (M.op X2 X2) (M.op X3 X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq18 (M.op (M.op X2 X2) (M.op X3 X0)) X1 (M.op (M.op X4 X4) X3) X5
       have i₂ := eq18 X3 X2 X0 X4
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq182 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op X1 X1) X0) (M.op X3 X0)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq142 X0 X1 x X3 X4 x
       have i₂ := eq124 (M.op X3 X0) x x
       grind)
    | exact superpose eq124 eq142
    | exact resolve eq142 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq326 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (M.op X0 X0)
       have i₂ := eq60 X0 (σ X1)
       grind)
    | exact superpose eq60 eq39
    | exact resolve eq39 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq50 (σ X0) X1
       grind)
    | (have i₁ := eq31 X0 X0
       have i₂ := eq50 X0 (σ X0)
       grind)
    | exact superpose eq50 eq31
    | exact resolve eq31 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq14
    | (have j1 := eq31 x y
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq774 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (k X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (τ (M.op X0 X0))
       have i₂ := eq326 X0 (σ X1)
       grind)
    | exact superpose eq326 eq39
    | exact resolve eq39 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq326
  have eq2259 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) X2) = (M.op (M.op X1 X2) (M.op (M.op X3 X3) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X4 X4) X2) (M.op X1 X2) X3
       have i₂ := eq182 X2 X4 X1 X0
       grind)
    | exact superpose eq182 eq8
    | exact resolve eq8 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq2260 : ∀ X1 X2 X4 : G, (M.op (M.op X4 X4) X2) = (M.op (M.op X1 X2) X1) := by
    intro X1 X2 X4
    first
    | (have i₁ := eq2259 x X1 X2 x X4
       have i₂ := eq124 X1 x x
       grind)
    | exact superpose eq124 eq2259
    | exact resolve eq2259 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259
  have eq2488 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X1) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124 X1 X2 x
       have i₂ := eq2260 X0 X1 x
       grind)
    | (have i₁ := eq124 X2 X1 X2
       have i₂ := eq2260 X2 X2 x
       grind)
    | exact superpose eq2260 eq124
    | exact resolve eq124 eq2260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq2260
  have eq4852 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq415 X1 (M.op X0 X0)
       have i₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact superpose eq60 eq415
    | (have j0 := eq415 X1 (M.op X0 X0)
       grind)
    | exact resolve eq415 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4857 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq415 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq774 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq774 eq415
    | (have j0 := eq415 X1 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq415 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq4952 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X1)
       have i₂ := eq415 X0 (τ X1)
       grind)
    | exact superpose eq415 eq17
    | (have j1 := eq415 X0 (τ X1)
       grind)
    | exact resolve eq17 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq415
  have eq4974 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq4857 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4857
  have eq4978 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4852 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4852
  have eq4989 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4952 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4952
    | (have j0 := eq4952 X0 X1
       grind)
    | exact resolve eq4952 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4952
  have eq5025 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4974 X0 X1
       have i₂ := eq10 (τ (M.op X0 X0))
       grind)
    | exact superpose eq10 eq4974
    | exact resolve eq4974 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4974
  have eq5035 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4989 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4989
    | (have j0 := eq4989 X0 X1
       grind)
    | exact resolve eq4989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4989
  have eq5058 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq432
       have i₂ := eq62 X0 x y
       grind)
    | exact superpose eq62 eq432
    | (have j1 := eq62 (σ x) x (σ y)
       grind)
    | exact resolve eq432 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq432
  have eq5064 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq5058 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5058
  have eq5173 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (σ (M.op X0 X0)) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2488 X2 X2 X1
       have i₂ := eq4978 X0 X2
       grind)
    | exact superpose eq4978 eq2488
    | exact resolve eq2488 eq4978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2488 eq4978
  have eq30475 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X1 X2
       have i₂ := eq5035 X2 X0
       grind)
    | exact superpose eq5035 eq50
    | (have j1 := eq5035 X1 X0
       grind)
    | exact resolve eq50 eq5035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq30754 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5035 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46085 : ∀ X0 X2 X3 : G, (k X2 X0) = X0 ∨ (M.op X3 X3) = (k X0 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq60 X2 X2
       have i₂ := eq30475 X0 x X2
       grind)
    | (have i₁ := eq60 X0 X2
       have i₂ := eq30475 (M.op X0 X0) x X2
       grind)
    | exact superpose eq30475 eq60
    | (have j1 := eq30475 X0 X3 X2
       grind)
    | exact resolve eq60 eq30475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq30475
  have eq66856 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46085 X0 x X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46085
  have eq66862 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66856 X0 X1
       have j1 := eq5035 X1 X0
       grind)
    | (have r₁ := eq66856 (k X1 X1) X0
       have r₂ := eq5035 X0 X1
       grind)
    | (have r₁ := eq66856 X1 X0
       have r₂ := eq5035 X0 X1
       grind)
    | (have r₁ := eq66856 (M.op X0 X0) X1
       have r₂ := eq5035 X0 (M.op X1 X1)
       grind)
    | exact resolve eq66856 eq5035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5035 eq66856
  have eq67900 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30754 X2 X1
       have i₂ := eq66862 X1 X0
       grind)
    | exact superpose eq66862 eq30754
    | (have j0 := eq30754 X2 X1
       grind)
    | (have r₁ := eq30754 X0 (M.op X1 X1)
       have r₂ := eq66862 (M.op X1 X1) X1
       grind)
    | exact resolve eq30754 eq66862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30754 eq66862
  have eq69448 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5025 (σ x) X0
       have i₂ := eq5064 X1
       grind)
    | exact superpose eq5064 eq5025
    | (have j1 := eq5064 X1
       grind)
    | exact resolve eq5025 eq5064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5025 eq5064
  have eq69767 : ∀ X0 X1 : G, (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69448 X0 X1
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq69448
    | (have j0 := eq69448 X0 X0
       grind)
    | exact resolve eq69448 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69448
  have eq69776 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq69767 X0 X0
       have j1 := eq67900 X0 y X0
       grind)
    | (have r₁ := eq69767 X0 x
       have r₂ := eq67900 X0 y x
       grind)
    | (have r₁ := eq69767 X0 X0
       have r₂ := eq67900 X0 y x
       grind)
    | exact resolve eq69767 eq67900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67900 eq69767
  have eq70032 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 X0 X0
       have i₂ := eq69776 (M.op X0 X0)
       grind)
    | exact superpose eq69776 eq8
    | exact resolve eq8 eq69776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70038 : ∀ X0 : G, y = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5173 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq69776 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq69776 eq5173
    | exact resolve eq5173 eq69776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5173
  have eq70125 : y = (σ y) := by
    first
    | (have i₁ := eq70038 x
       have i₂ := eq69776 x
       grind)
    | exact superpose eq69776 eq70038
    | exact resolve eq70038 eq69776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69776 eq70038
  have eq70822 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq70125
       grind)
    | exact superpose eq70125 eq14
    | exact resolve eq14 eq70125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70125
  have eq70856 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq70822
       have i₂ := eq70032 (σ x)
       grind)
    | exact superpose eq70032 eq70822
    | exact resolve eq70822 eq70032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70822
  have eq70866 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq70856
       have i₂ := eq70032 x
       grind)
    | exact superpose eq70032 eq70856
    | exact resolve eq70856 eq70032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70032 eq70856
  have eq70867 : False := by grind
  exact eq70867

/-- `Equation1053`: `x = x ◇ ((y ◇ (y ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation1053 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1053 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1053.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2)) = X0 := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2)))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X0 (M.op (M.op X1 (M.op X1 X2)) X2)
       have i₂ := eq8 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2))) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq23 X0 x x X3
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq23
    | exact resolve eq23 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact superpose eq24 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq56 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq118 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 (M.op X0 X0)
       have i₂ := eq35 X0 (σ X1)
       grind)
    | exact superpose eq35 eq56
    | exact resolve eq56 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq186 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq46 X2 X0
       grind)
    | exact superpose eq46 eq24
    | (have j1 := eq46 X2 X0
       grind)
    | exact resolve eq24 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq46 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq467 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq512 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq467 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq467
    | (have j0 := eq467 X0 X1
       grind)
    | exact resolve eq467 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq1255 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq187 (M.op X0 X0)
       have i₂ := eq35 X0 (M.op X0 X0)
       grind)
    | exact superpose eq35 eq187
    | (have j0 := eq187 (M.op X0 X0)
       grind)
    | exact resolve eq187 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1269 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq187 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq187
    | (have j0 := eq187 (τ X0)
       grind)
    | exact resolve eq187 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq187
  have eq1282 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1255 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq1287 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1269 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1269
    | (have j0 := eq1269 X0
       grind)
    | exact resolve eq1269 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269
  have eq1296 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1287 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1287
    | (have j0 := eq1287 X0
       grind)
    | exact resolve eq1287 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287
  have eq1474 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ (M.op X0 X0)) X1
       have i₂ := eq1282 X0
       grind)
    | exact superpose eq1282 eq24
    | exact resolve eq24 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq1551 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1474 X0 X1
       have i₂ := eq512 X2 X0
       grind)
    | exact superpose eq512 eq1474
    | (have j1 := eq512 X2 X0
       grind)
    | exact resolve eq1474 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq1474
  have eq1651 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq186 y X0 x
       grind)
    | exact superpose eq186 eq14
    | (have j1 := eq186 y X0 x
       grind)
    | exact resolve eq14 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1678 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1651 X0
       have j1 := eq1551 y X0 x
       grind)
    | (have r₁ := eq1651 X0
       have r₂ := eq1551 y x x
       grind)
    | exact resolve eq1651 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551 eq1651
  have eq1691 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq118 (σ y) x
       have i₂ := eq1678 (σ y)
       grind)
    | exact superpose eq1678 eq118
    | exact resolve eq118 eq1678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1702 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1678 (σ x)
       grind)
    | exact superpose eq1678 eq14
    | exact resolve eq14 eq1678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678
  have eq1714 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1691 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1691
    | exact resolve eq1691 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691
  have eq1836 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1296 y
       have i₂ := eq1714 y
       grind)
    | exact superpose eq1714 eq1296
    | (have j0 := eq1296 y
       grind)
    | (have r₁ := eq1296 y
       have r₂ := eq1714 y
       grind)
    | exact resolve eq1296 eq1714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296 eq1714
  have eq1852 : y = (M.op y y) := by grind
  clear eq1836
  have eq1961 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq1852
       grind)
    | exact superpose eq1852 eq24
    | exact resolve eq24 eq1852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1852
  have eq2363 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1702
       have i₂ := eq1961 x
       grind)
    | exact superpose eq1961 eq1702
    | exact resolve eq1702 eq1961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1702 eq1961
  have eq2364 : False := by grind
  exact eq2364

/-- `Equation1256`: `x = x ◇ (((y ◇ y) ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation1256 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1256 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1256.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X2) X2)) = X0 := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) X2) X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X0 (M.op (M.op (M.op X1 X1) X2) X2)
       have i₂ := eq8 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) X2) X2)) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq23 X0 x x X3
       have i₂ := eq8 (M.op X0 X0) x x
       grind)
    | exact superpose eq8 eq23
    | exact resolve eq23 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact superpose eq24 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq48 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq57 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq131 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 (M.op X0 X0)
       have i₂ := eq35 X0 (σ X1)
       grind)
    | exact superpose eq35 eq57
    | exact resolve eq57 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq254 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq47 X2 X0
       grind)
    | exact superpose eq47 eq24
    | (have j1 := eq47 X2 X0
       grind)
    | exact resolve eq24 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq47 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq599 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq650 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq599 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq599
    | (have j0 := eq599 X0 X1
       grind)
    | exact resolve eq599 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq1456 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq259 (M.op X0 X0)
       have i₂ := eq35 X0 (M.op X0 X0)
       grind)
    | exact superpose eq35 eq259
    | (have j0 := eq259 (M.op X0 X0)
       grind)
    | exact resolve eq259 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1471 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq259 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq259
    | (have j0 := eq259 (τ X0)
       grind)
    | exact resolve eq259 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq259
  have eq1483 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1456 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456
  have eq1488 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1471 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1471
    | (have j0 := eq1471 X0
       grind)
    | exact resolve eq1471 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471
  have eq1497 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1488 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1488
    | (have j0 := eq1488 X0
       grind)
    | exact resolve eq1488 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1679 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ (M.op X0 X0)) X1
       have i₂ := eq1483 X0
       grind)
    | exact superpose eq1483 eq24
    | exact resolve eq24 eq1483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483
  have eq1765 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1679 X0 X1
       have i₂ := eq650 X2 X0
       grind)
    | exact superpose eq650 eq1679
    | (have j1 := eq650 X2 X0
       grind)
    | exact resolve eq1679 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq1679
  have eq1883 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq254 y X0 x
       grind)
    | exact superpose eq254 eq14
    | (have j1 := eq254 y X0 x
       grind)
    | exact resolve eq14 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq1911 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1883 X0
       have j1 := eq1765 y X0 x
       grind)
    | (have r₁ := eq1883 X0
       have r₂ := eq1765 y x x
       grind)
    | exact resolve eq1883 eq1765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765 eq1883
  have eq1926 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq131 (σ y) x
       have i₂ := eq1911 (σ y)
       grind)
    | exact superpose eq1911 eq131
    | exact resolve eq131 eq1911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq1942 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1911 (σ x)
       grind)
    | exact superpose eq1911 eq14
    | exact resolve eq14 eq1911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq1960 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1926 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1926
    | exact resolve eq1926 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926
  have eq2088 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1497 y
       have i₂ := eq1960 y
       grind)
    | exact superpose eq1960 eq1497
    | (have j0 := eq1497 y
       grind)
    | (have r₁ := eq1497 y
       have r₂ := eq1960 y
       grind)
    | exact resolve eq1497 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497 eq1960
  have eq2104 : y = (M.op y y) := by grind
  clear eq2088
  have eq2219 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq2104
       grind)
    | exact superpose eq2104 eq24
    | exact resolve eq24 eq2104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2104
  have eq2740 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1942
       have i₂ := eq2219 x
       grind)
    | exact superpose eq2219 eq1942
    | exact resolve eq1942 eq2219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942 eq2219
  have eq2741 : False := by grind
  exact eq2741

/-- `Equation1264`: `x = x ◇ (((y ◇ z) ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation1264 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1264 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1264.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = X0 := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X0 (M.op (M.op (M.op X1 X2) X1) X2)
       have i₂ := eq8 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq23 X0 x x X3
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq23
    | exact resolve eq23 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact superpose eq24 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq56 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq129 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 (M.op X0 X0)
       have i₂ := eq35 X0 (σ X1)
       grind)
    | exact superpose eq35 eq56
    | exact resolve eq56 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq249 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq46 X2 X0
       grind)
    | exact superpose eq46 eq24
    | (have j1 := eq46 X2 X0
       grind)
    | exact resolve eq24 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq46 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq581 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq632 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq581 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq581
    | (have j0 := eq581 X0 X1
       grind)
    | exact resolve eq581 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq1583 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq250 (M.op X0 X0)
       have i₂ := eq35 X0 (M.op X0 X0)
       grind)
    | exact superpose eq35 eq250
    | (have j0 := eq250 (M.op X0 X0)
       grind)
    | exact resolve eq250 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1598 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq250 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq250
    | (have j0 := eq250 (τ X0)
       grind)
    | exact resolve eq250 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq250
  have eq1611 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1583 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583
  have eq1617 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1598 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1598
    | (have j0 := eq1598 X0
       grind)
    | exact resolve eq1598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq1626 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1617 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1617
    | (have j0 := eq1617 X0
       grind)
    | exact resolve eq1617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617
  have eq1815 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ (M.op X0 X0)) X1
       have i₂ := eq1611 X0
       grind)
    | exact superpose eq1611 eq24
    | exact resolve eq24 eq1611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1611
  have eq1910 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1815 X0 X1
       have i₂ := eq632 X2 X0
       grind)
    | exact superpose eq632 eq1815
    | (have j1 := eq632 X2 X0
       grind)
    | exact resolve eq1815 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq1815
  have eq2053 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq249 y X0 x
       grind)
    | exact superpose eq249 eq14
    | (have j1 := eq249 y X0 x
       grind)
    | exact resolve eq14 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq2083 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq2053 X0
       have j1 := eq1910 y X0 x
       grind)
    | (have r₁ := eq2053 X0
       have r₂ := eq1910 y x x
       grind)
    | exact resolve eq2053 eq1910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1910 eq2053
  have eq2098 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq129 (σ y) x
       have i₂ := eq2083 (σ y)
       grind)
    | exact superpose eq2083 eq129
    | exact resolve eq129 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq2122 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2083 (σ x)
       grind)
    | exact superpose eq2083 eq14
    | exact resolve eq14 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083
  have eq2144 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq2098 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2098
    | exact resolve eq2098 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2098
  have eq2271 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1626 y
       have i₂ := eq2144 y
       grind)
    | exact superpose eq2144 eq1626
    | (have j0 := eq1626 y
       grind)
    | (have r₁ := eq1626 y
       have r₂ := eq2144 y
       grind)
    | exact resolve eq1626 eq2144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626 eq2144
  have eq2287 : y = (M.op y y) := by grind
  clear eq2271
  have eq2397 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq2287
       grind)
    | exact superpose eq2287 eq24
    | exact resolve eq24 eq2287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2287
  have eq2913 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2122
       have i₂ := eq2397 x
       grind)
    | exact superpose eq2397 eq2122
    | exact resolve eq2122 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122 eq2397
  have eq2914 : False := by grind
  exact eq2914

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_pxx_pyx_Equation1701 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1701 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq136 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq140 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq136 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq136 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq136 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq163 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq140 (σ X1) (σ X0)
       grind)
    | exact superpose eq140 eq13
    | exact resolve eq13 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq163 X0 X1
       have i₂ := eq140 X1 X0
       grind)
    | exact superpose eq140 eq163
    | exact resolve eq163 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq163
  have eq1068 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq168 x y
       grind)
    | exact superpose eq168 eq14
    | (have r₁ := eq14
       have r₂ := eq168 x y
       grind)
    | exact resolve eq14 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq1090 : False := by grind
  exact eq1090

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

/-- `Equation3591`: `x ◇ y = z ◇ ((x ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pyx_Equation3591 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3591 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3591.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op (M.op X0 X2) X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 (M.op X2 X3)) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 (M.op X2 X3)) X1) X3
       have i₂ := eq8 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq41 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq41 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq67 : ∀ X0 X1 X2 : G, (τ X0) = (k X1 (τ X0)) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq47 X0 (σ X1) X2
       grind)
    | exact superpose eq47 eq28
    | (have j1 := eq47 (τ X0) X1 X2
       grind)
    | exact resolve eq28 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq47 X0 (τ X1) X2
       grind)
    | exact superpose eq47 eq15
    | (have j1 := eq47 (σ X0) X1 X2
       grind)
    | exact resolve eq15 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq47 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq47 eq13
    | (have j1 := eq47 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq47 X0 X2 (τ X1)
       grind)
    | exact superpose eq47 eq15
    | (have j1 := eq47 X0 X2 X2
       grind)
    | exact resolve eq15 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq84 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op (M.op X0 X2) X1)) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X2 X0 X1
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op (M.op (M.op (M.op (M.op X4 X0) X5) X2) (M.op (M.op X4 X5) X1)) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1) X2 X3
       have i₂ := eq21 X4 X5 X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X4)) X1)) = (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 X3 X4 X2 (M.op (M.op X0 (M.op X3 X4)) X1)
       have i₂ := eq8 X0 X1 (M.op X3 X4)
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (M.op X2 X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X0) (M.op (M.op X2 X3) X1) X3
       have i₂ := eq21 X2 X3 X0 X1
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X3) X4) = (M.op (M.op (M.op X2 X3) X1) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X2 X0) X3) X4 (M.op (M.op X2 X3) X1)
       have i₂ := eq21 X2 X3 X0 X1
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1))) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq91 X0 X1 X2 X3 X4 X5
       have i₂ := eq93 (M.op X0 X1) X3 X2 (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1)
       grind)
    | exact superpose eq93 eq91
    | exact resolve eq91 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq109 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X2 X1)) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq84 X0 X1 X2 X3
       have i₂ := eq96 X2 X1 X0 X2
       grind)
    | exact superpose eq96 eq84
    | (have j0 := eq84 X0 X1 X2 X3
       grind)
    | exact resolve eq84 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq102 X0 X1 X2 X3 x x
       have i₂ := eq21 x x X0 X1
       grind)
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq129 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) (M.op X4 X5)) = (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq22 X4 X5 X3 (M.op (M.op X1 (M.op X3 X0)) X2)
       have i₂ := eq22 X1 X2 X3 X0
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op (M.op X2 X0) X3) X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 (M.op (M.op X2 X0) X3) X4 (M.op X2 X3) X1
       have i₂ := eq21 X2 X3 X0 X1
       grind)
    | exact superpose eq21 eq22
    | exact resolve eq22 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) X5) (M.op (M.op X3 X5) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 X3 X5 (M.op (M.op X1 (M.op X3 X0)) X2) X4
       have i₂ := eq22 X1 X2 X3 X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op (M.op (M.op X4 X3) X5) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 X4 X5 X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)
       have i₂ := eq22 X1 X2 (M.op X4 X5) X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op X3 (M.op (M.op X0 (M.op X4 X5)) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq144 X0 X1 X2 X3 X4 X5
       have i₂ := eq93 X0 (M.op X1 X2) X3 X4 X5
       grind)
    | exact superpose eq93 eq144
    | exact resolve eq144 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq150 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 X3) (M.op X1 X2)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq141 X0 X1 X2 X3 X4 x
       have i₂ := eq98 X3 x X0 (M.op X1 X2) X4
       grind)
    | exact superpose eq98 eq141
    | exact resolve eq141 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq141
  have eq157 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) = (M.op (M.op X3 X0) (M.op (M.op X4 (M.op X1 X2)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq129 X0 X1 X2 X3 X4 X5
       have i₂ := eq93 X4 X5 (M.op X3 X0) X1 X2
       grind)
    | exact superpose eq93 eq129
    | exact resolve eq129 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq173 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq68 X0 (σ X1) X2
       grind)
    | exact superpose eq68 eq13
    | (have j1 := eq68 X0 X1 X2
       grind)
    | exact resolve eq13 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq224 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 (σ X0) X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq67
    | (have j0 := eq67 (σ X0) X1 X2
       grind)
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq289 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq43 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq957 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X1 (σ X0) X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq74
    | (have j0 := eq74 X1 X1 X2
       grind)
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1036 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq957 X0 X1 X2
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq957
    | (have j0 := eq957 X0 X1 X2
       grind)
    | exact resolve eq957 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1282 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1036 X2 X0 (τ X1)
       grind)
    | exact superpose eq1036 eq15
    | (have j1 := eq1036 X2 X0 X2
       grind)
    | exact resolve eq15 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq1036
  have eq1323 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X2) X1) (M.op X3 X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq96 X3 X4 X2 (M.op (M.op X0 X2) X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq96
    | exact resolve eq96 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1357 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2 (M.op X0 X1)
       have i₂ := eq96 X1 X2 X0 (M.op X0 X1)
       grind)
    | exact superpose eq96 eq8
    | exact resolve eq8 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1358 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X1) X4)) = (M.op (M.op X3 X0) (M.op (M.op X0 (M.op X1 X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 (M.op X3 X1) X4 (M.op X3 X0) X2
       have i₂ := eq96 X1 X2 X3 X0
       grind)
    | exact superpose eq96 eq22
    | exact resolve eq22 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1360 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op (M.op (M.op X3 X0) X2) (M.op (M.op X0 (M.op X1 X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X3 X1) X4 (M.op (M.op X3 X0) X2)
       have i₂ := eq96 X1 X2 X3 X0
       grind)
    | exact superpose eq96 eq8
    | exact resolve eq8 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1363 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X4 X5)) = (M.op (M.op X3 X1) (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq22 X4 X5 (M.op X3 X1) (M.op (M.op X3 X0) X2)
       have i₂ := eq96 X1 X2 X3 X0
       grind)
    | exact superpose eq96 eq22
    | exact resolve eq22 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1372 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X4 X5)) = (M.op X3 (M.op (M.op X4 (M.op X1 (M.op X0 (M.op X1 X2)))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1363 X0 X1 X2 X3 X4 X5
       have i₂ := eq157 X1 X0 (M.op X1 X2) X3 X4 X5
       grind)
    | exact superpose eq157 eq1363
    | exact resolve eq1363 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq1375 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X0 (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1360 X0 X1 X2 X3 X4
       have i₂ := eq93 (M.op X0 (M.op X1 X2)) X4 X0 X3 X2
       grind)
    | exact superpose eq93 eq1360
    | exact resolve eq1360 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360
  have eq1377 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X1) X4)) = (M.op X3 (M.op (M.op X0 (M.op X0 (M.op X1 X2))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1358 X0 X1 X2 X3 X4
       have i₂ := eq157 X0 X1 X2 X3 X0 X4
       grind)
    | exact superpose eq157 eq1358
    | exact resolve eq1358 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq1358
  have eq1392 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 (M.op X0 X1)) X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1323 X0 X1 X2 X3 X4
       have i₂ := eq93 X3 X4 X2 X0 X1
       grind)
    | exact superpose eq93 eq1323
    | exact resolve eq1323 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1397 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 (M.op X1 (M.op X0 (M.op X1 X2)))) X5)) = (M.op X0 (M.op (M.op X4 (M.op X3 X2)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1372 X0 X1 X2 X3 X4 X5
       have i₂ := eq93 X4 X5 X0 X3 X2
       grind)
    | exact superpose eq93 eq1372
    | exact resolve eq1372 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq1372
  have eq1400 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X0 (M.op (M.op (M.op X2 X1) (M.op X0 (M.op X3 X2))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1375 X0 X1 X2 X3 X4
       have i₂ := eq150 X2 X0 (M.op X3 X2) X1 X4
       grind)
    | (have i₁ := eq1375 X0 X1 X2 X1 X4
       have i₂ := eq150 X0 X1 X2 (M.op X1 X2) X4
       grind)
    | exact superpose eq150 eq1375
    | exact resolve eq1375 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1410 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op (M.op X3 X2) (M.op (M.op X2 X1) X4)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1400 x X1 X2 X3 X4
       have i₂ := eq22 (M.op X2 X1) X4 x (M.op X3 X2)
       grind)
    | exact superpose eq22 eq1400
    | exact resolve eq1400 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1415 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X3 (M.op (M.op X2 (M.op X2 X1)) X4)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1410 X1 X2 X3 X4
       have i₂ := eq1392 X2 X1 X3 X2 X4
       grind)
    | (have i₁ := eq1410 (M.op x X1) X3 X3 X4
       have i₂ := eq1392 x X1 (M.op X3 X3) X3 X4
       grind)
    | exact superpose eq1392 eq1410
    | exact resolve eq1410 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1423 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1357 X3 (M.op (M.op X1 (M.op X3 X0)) X2) X4
       have i₂ := eq22 X1 X2 X3 X0
       grind)
    | exact superpose eq22 eq1357
    | exact resolve eq1357 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1435 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X3) X1)) = (M.op (M.op X2 X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1357 X2 X3 (M.op (M.op X0 X3) X1)
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq1357
    | exact resolve eq1357 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1452 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op (M.op X0 X2) X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X3 X2 (M.op X3 X1)
       have i₂ := eq1357 X0 X3 X1
       grind)
    | exact superpose eq1357 eq21
    | exact resolve eq21 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1454 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X0 X1) X0
       have i₂ := eq1357 X2 X0 X1
       grind)
    | exact superpose eq1357 eq8
    | exact resolve eq8 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1457 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X2 (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 (M.op X0 X1) X3 X1 X2
       have i₂ := eq1357 X0 X1 X2
       grind)
    | exact superpose eq1357 eq22
    | exact resolve eq22 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1458 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op x x)
       have i₂ := eq1357 x x x
       grind)
    | exact superpose eq1357 eq11
    | (have r₁ := eq11 X0 (M.op x x)
       have r₂ := eq1357 x x x
       grind)
    | exact resolve eq11 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1461 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op (M.op X0 X1) X4) (M.op (M.op (M.op X0 X2) X4) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 (M.op X0 X2) X4 (M.op X2 X1) X3
       have i₂ := eq1357 X0 X2 X1
       grind)
    | exact superpose eq1357 eq21
    | exact resolve eq21 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1470 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1458 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1458
  have eq1475 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X4) (M.op (M.op X2 (M.op (M.op X0 X1) X4)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1461 X0 X1 X2 X3 X4
       have i₂ := eq135 X2 (M.op (M.op X0 X1) X4) X0 X4 X3
       grind)
    | (have i₁ := eq1461 X0 X1 X2 X4 X1
       have i₂ := eq135 (M.op X0 X2) X1 (M.op X0 X1) X1 X4
       grind)
    | exact superpose eq135 eq1461
    | exact resolve eq1461 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq1461
  have eq1479 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X0 (M.op (M.op (M.op X0 X2) X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1452 X0 X1 X2 X3
       have i₂ := eq1454 X0 X1 (M.op (M.op X0 X2) X3)
       grind)
    | (have i₁ := eq1452 X0 X1 X2 X3
       have i₂ := eq1454 (M.op (M.op X0 X2) X3) X1 X0
       grind)
    | exact superpose eq1454 eq1452
    | exact resolve eq1452 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq1454
  have eq1492 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op X2 (M.op (M.op (M.op X1 (M.op X3 X0)) (M.op X0 (M.op X1 X2))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1423 X0 X1 X2 X3 X4
       have i₂ := eq1457 (M.op X1 (M.op X3 X0)) (M.op X0 (M.op X1 X2)) X2 X4
       grind)
    | (have i₁ := eq1423 X0 X1 X2 X3 X4
       have i₂ := eq1457 (M.op X1 (M.op X3 X0)) X2 (M.op X0 (M.op X1 X2)) X4
       grind)
    | exact superpose eq1457 eq1423
    | exact resolve eq1423 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423
  have eq1498 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X4) (M.op (M.op X4 (M.op X0 X1)) (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1475 X0 X1 X2 X3 X4
       have i₂ := eq148 X4 X2 X3 (M.op X0 X4) X0 X1
       grind)
    | (have i₁ := eq1475 X0 X1 X0 (M.op X1 X2) x
       have i₂ := eq148 X0 X1 X2 (M.op X0 x) (M.op X0 X1) x
       grind)
    | exact superpose eq148 eq1475
    | exact resolve eq1475 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq1508 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op X2 (M.op (M.op (M.op X0 X3) (M.op X1 (M.op X0 (M.op X1 X2)))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1492 X0 X1 X2 X3 X4
       have i₂ := eq150 X0 X1 (M.op X0 (M.op X1 X2)) X3 X4
       grind)
    | (have i₁ := eq1492 X1 X0 X2 X3 X4
       have i₂ := eq150 X0 X1 (M.op X0 X2) (M.op X3 X1) X4
       grind)
    | exact superpose eq150 eq1492
    | exact resolve eq1492 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq1492
  have eq1512 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op X0 (M.op (M.op X4 (M.op X4 (M.op X0 X1))) (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1498 X0 X1 X2 X3 X4
       have i₂ := eq1392 X4 (M.op X0 X1) X0 X4 (M.op X2 X3)
       grind)
    | (have i₁ := eq1498 X0 X1 X2 X3 X3
       have i₂ := eq1392 X0 X1 (M.op X0 X3) X3 (M.op X2 X3)
       grind)
    | exact superpose eq1392 eq1498
    | exact resolve eq1498 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392 eq1498
  have eq1516 : ∀ X0 X2 X3 X4 : G, (M.op X3 X4) = (M.op X0 (M.op (M.op (M.op X0 X3) (M.op X2 X2)) X4)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1508 X0 x X2 X3 X4
       have i₂ := eq1397 X0 x X2 X2 (M.op X0 X3) X4
       grind)
    | exact superpose eq1397 eq1508
    | exact resolve eq1508 eq1397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397 eq1508
  have eq1518 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op X1 (M.op (M.op X0 X0) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1512 X0 X1 X2 X3 x
       have i₂ := eq1377 x X0 X1 X0 (M.op X2 X3)
       grind)
    | exact superpose eq1377 eq1512
    | exact resolve eq1512 eq1377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377 eq1512
  have eq1521 : ∀ X2 X3 X4 : G, (M.op X3 X4) = (M.op X3 (M.op (M.op X2 X2) X4)) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq1516 x X2 X3 X4
       have i₂ := eq1479 x X4 X3 (M.op X2 X2)
       grind)
    | exact superpose eq1479 eq1516
    | exact resolve eq1516 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479 eq1516
  have eq1523 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op X1 (M.op X0 (M.op (M.op X2 X0) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1518 X0 X1 X2 X3
       have i₂ := eq1435 X2 X3 X0 X0
       grind)
    | (have i₁ := eq1518 X0 X1 (M.op X0 X3) X1
       have i₂ := eq1435 X0 X1 (M.op X0 X0) X3
       grind)
    | exact superpose eq1435 eq1518
    | exact resolve eq1518 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435 eq1518
  have eq1525 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op (M.op X2 X1) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1523 x X1 X2 X3
       have i₂ := eq8 X2 X3 x
       grind)
    | exact superpose eq8 eq1523
    | exact resolve eq1523 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1572 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X2 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1)
       have i₂ := eq110 X3 X4 X0 X1
       grind)
    | exact superpose eq110 eq8
    | exact resolve eq8 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq1612 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op X0 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1)) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1572 X0 X1 X2 X3 X4
       have i₂ := eq1457 X0 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1) X1 X2
       grind)
    | (have i₁ := eq1572 X0 X1 X2 X3 X4
       have i₂ := eq1457 X0 X1 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1) X2
       grind)
    | exact superpose eq1457 eq1572
    | exact resolve eq1572 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572
  have eq1650 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op X1 (M.op (M.op X3 X4) (M.op X3 X4))) (M.op X0 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1612 X0 X1 X2 X3 X4
       have i₂ := eq148 X1 X0 X2 X1 (M.op X3 X4) (M.op X3 X4)
       grind)
    | (have i₁ := eq1612 X0 x (M.op X1 X2) X3 X4
       have i₂ := eq148 X0 X1 X2 x (M.op (M.op X3 X4) (M.op X3 X4)) x
       grind)
    | exact superpose eq148 eq1612
    | exact resolve eq1612 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq1681 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1650 X0 X1 X2 X3 X4
       have i₂ := eq148 (M.op X3 X4) X1 (M.op X0 X2) X1 X3 X4
       grind)
    | (have i₁ := eq1650 X1 X0 X2 X3 X4
       have i₂ := eq148 X0 X1 X2 X0 (M.op X3 X4) (M.op X3 X4)
       grind)
    | exact superpose eq148 eq1650
    | exact resolve eq1650 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq1650
  have eq1707 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1681 X0 X1 X2 x x
       have i₂ := eq1521 (M.op x x) X1 (M.op X1 (M.op X0 X2))
       grind)
    | (have i₁ := eq1681 X0 x X2 x x
       have i₂ := eq1521 X2 x (M.op (M.op (M.op x x) (M.op x x)) (M.op x (M.op X0 X2)))
       grind)
    | exact superpose eq1521 eq1681
    | exact resolve eq1681 eq1521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521 eq1681
  have eq1869 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq289 (M.op X0 X0)
       have i₂ := eq1470 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1470 eq289
    | (have j0 := eq289 (M.op X0 X0)
       grind)
    | exact resolve eq289 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1879 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq289 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq289
    | (have j0 := eq289 (τ X0)
       grind)
    | exact resolve eq289 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq289
  have eq1887 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1869 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq1893 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1879 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1879
    | (have j0 := eq1879 X0
       grind)
    | exact resolve eq1879 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879
  have eq1901 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1893 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1893
    | (have j0 := eq1893 X0
       grind)
    | exact resolve eq1893 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1893
  have eq2070 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1707 X1 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq1707
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq1707 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2245 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ X1 ∨ (M.op X0 (M.op X0 X1)) = (k X2 X1) ∨ (M.op X1 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq109 X1 X1 X2 X3
       grind)
    | exact superpose eq109 eq11
    | (have j1 := eq109 X1 X1 X2 X3
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq2387 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (k X2 X1) ∨ (M.op X1 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq2245 X0 X1 X2 X3
       have j1 := eq2070 X1 X1 X3
       grind)
    | (have r₁ := eq2245 X1 X0 X2 X3
       have r₂ := eq2070 X0 X1 X2
       grind)
    | exact resolve eq2245 eq2070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070 eq2245
  have eq4508 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq72 x y X0
       grind)
    | exact superpose eq72 eq14
    | (have j1 := eq72 x x X0
       grind)
    | exact resolve eq14 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq4588 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq4508 X0
       have j1 := eq1282 x X0 x
       grind)
    | (have r₁ := eq4508 X0
       have r₂ := eq1282 x x y
       grind)
    | exact resolve eq4508 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282 eq4508
  have eq4631 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1901 (σ x)
       have i₂ := eq4588 (σ x)
       grind)
    | exact superpose eq4588 eq1901
    | (have j0 := eq1901 (σ x)
       grind)
    | (have r₁ := eq1901 (σ x)
       have r₂ := eq4588 (σ x)
       grind)
    | exact resolve eq1901 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4648 : ∀ X0 : G, (τ (σ x)) = (k X0 (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ x)
       have i₂ := eq4588 (σ X0)
       grind)
    | exact superpose eq4588 eq28
    | exact resolve eq28 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4588
  have eq4653 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4631
  have eq4654 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq4648 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq4648
    | exact resolve eq4648 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4648
  have eq4805 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1901 x
       have i₂ := eq4654 x
       grind)
    | exact superpose eq4654 eq1901
    | (have j0 := eq1901 x
       grind)
    | (have r₁ := eq1901 x
       have r₂ := eq4654 x
       grind)
    | exact resolve eq1901 eq4654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901 eq4654
  have eq4824 : x = (M.op x x) := by grind
  clear eq4805
  have eq4844 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) (M.op (M.op x X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 x X1 x X0
       have i₂ := eq4824
       grind)
    | exact superpose eq4824 eq21
    | exact resolve eq21 eq4824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq4859 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1707 x x x
       have i₂ := eq4824
       grind)
    | exact superpose eq4824 eq1707
    | exact resolve eq1707 eq4824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4869 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op (M.op x (M.op x X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4844 X0 X1
       have i₂ := eq1457 x (M.op x X1) X1 X0
       grind)
    | (have i₁ := eq4844 X0 X1
       have i₂ := eq1457 x X1 (M.op x X1) X0
       grind)
    | exact superpose eq1457 eq4844
    | exact resolve eq4844 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457 eq4844
  have eq4874 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4869 X0 X1
       have i₂ := eq1415 X1 x X1 X0
       grind)
    | (have i₁ := eq4869 X0 (M.op x X1)
       have i₂ := eq1415 X1 x x (M.op (M.op x (M.op x (M.op x X1))) X0)
       grind)
    | exact superpose eq1415 eq4869
    | exact resolve eq4869 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415 eq4869
  have eq4876 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4874 X0 X1
       have i₂ := eq1525 X1 X1 X0
       grind)
    | exact superpose eq1525 eq4874
    | exact resolve eq4874 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525 eq4874
  have eq9519 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq1357 (σ x) (σ x) X0
       have i₂ := eq4653
       grind)
    | exact superpose eq4653 eq1357
    | exact resolve eq1357 eq4653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq9524 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1707 (σ x) x (σ x)
       have i₂ := eq4653
       grind)
    | exact superpose eq4653 eq1707
    | exact resolve eq1707 eq4653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707 eq4653
  have eq9527 : (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq9524 x
       have i₂ := eq4876 (σ x) x
       grind)
    | exact superpose eq4876 eq9524
    | exact resolve eq9524 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9524
  have eq9530 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq9519 X0
       have i₂ := eq4876 X0 (σ x)
       grind)
    | exact superpose eq4876 eq9519
    | exact resolve eq9519 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9519
  have eq15951 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq9530 (σ y)
       grind)
    | exact superpose eq9530 eq14
    | exact resolve eq14 eq9530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9530
  have eq140067 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op x (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4876 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq1887 X0
       grind)
    | exact superpose eq1887 eq4876
    | exact resolve eq4876 eq1887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140074 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op x (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq140067 X0
       have i₂ := eq1887 X0
       grind)
    | exact superpose eq1887 eq140067
    | exact resolve eq140067 eq1887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887 eq140067
  have eq145925 : ∀ X0 X1 : G, (σ X0) = (M.op x (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq140074 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq140074
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq140074 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140074
  have eq149127 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X2 (M.op X2 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2387 X0 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387
  have eq149130 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op x X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq149127 X0 X1 x
       have i₂ := eq4876 X1 x
       grind)
    | exact superpose eq4876 eq149127
    | (have j0 := eq149127 X0 X1 x
       grind)
    | (have r₁ := eq149127 (M.op X1 (M.op x X1)) X1 x
       have r₂ := eq4876 (M.op x X1) X1
       grind)
    | (have r₁ := eq149127 x x X1
       have r₂ := eq4876 x X1
       grind)
    | exact resolve eq149127 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149127
  have eq156481 : ∀ X0 X1 : G, (M.op x X0) ≠ (M.op x X1) ∨ (k (M.op X1 X0) X1) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq149130 (M.op X1 X0) X1
       have i₂ := eq4876 X0 X1
       grind)
    | exact superpose eq4876 eq149130
    | (have r₁ := eq149130 (M.op X0 X0) X0
       have r₂ := eq4876 X0 X0
       grind)
    | exact resolve eq149130 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4876 eq149130
  have eq288319 : ∀ X0 : G, (M.op x X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq156481 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156481
  have eq288673 : ∀ X0 X1 : G, (σ X0) = (σ (M.op x X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq173 X0 (M.op X0 X0) X1
       have i₂ := eq288319 X0
       grind)
    | exact superpose eq288319 eq173
    | (have j0 := eq173 X0 X1 X1
       grind)
    | exact resolve eq173 eq288319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq289258 : ∀ X0 : G, (σ y) ≠ (M.op x (σ y)) ∨ (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq15951
       have i₂ := eq288673 y X0
       grind)
    | exact superpose eq288673 eq15951
    | (have j1 := eq288673 y X0
       grind)
    | exact resolve eq15951 eq288673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288673
  have eq289320 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq289258 X0
       have j1 := eq145925 y X0
       grind)
    | (have r₁ := eq289258 X0
       have r₂ := eq145925 y x
       grind)
    | exact resolve eq289258 eq145925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145925 eq289258
  have eq289546 : ∀ X0 X1 : G, y = (M.op y X0) ∨ (k X1 (σ y)) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq224 y X0 X1
       have i₂ := eq289320 X0
       grind)
    | exact superpose eq289320 eq224
    | (have j0 := eq224 y X1 X1
       grind)
    | exact resolve eq224 eq289320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq310998 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4859 y
       have i₂ := eq289546 (M.op y x) X0
       grind)
    | exact superpose eq289546 eq4859
    | (have j1 := eq289546 X0 X0
       grind)
    | exact resolve eq4859 eq289546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4859 eq289546
  have eq311089 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq310998 (σ X0)
       grind)
    | exact superpose eq310998 eq13
    | exact resolve eq13 eq310998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310998
  have eq311102 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ y) (σ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq311089 X0
       have i₂ := eq289320 X0
       grind)
    | exact superpose eq289320 eq311089
    | exact resolve eq311089 eq289320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289320 eq311089
  have eq311186 : (M.op x (σ y)) = (k (σ (M.op y y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq288319 (σ y)
       have i₂ := eq311102 y
       grind)
    | exact superpose eq311102 eq288319
    | exact resolve eq288319 eq311102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311102
  have eq311215 : (M.op x (σ y)) = (σ (k (M.op y y) y)) ∨ x = y := by
    first
    | (have i₁ := eq311186
       have i₂ := eq13 (M.op y y) y
       grind)
    | exact superpose eq13 eq311186
    | exact resolve eq311186 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311186
  have eq311245 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq311215
       have i₂ := eq288319 y
       grind)
    | exact superpose eq288319 eq311215
    | exact resolve eq311215 eq288319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288319 eq311215
  have eq311249 : x = y := by
    first
    | (have r₁ := eq311245
       have r₂ := eq15951
       grind)
    | exact resolve eq311245 eq15951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311245
  have eq316079 : (M.op x (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq15951
       have i₂ := eq311249
       grind)
    | exact superpose eq311249 eq15951
    | exact resolve eq15951 eq311249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15951 eq311249
  have eq316098 : (σ x) ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq316079
       have i₂ := eq4824
       grind)
    | exact superpose eq4824 eq316079
    | exact resolve eq316079 eq4824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4824 eq316079
  have eq316104 : False := by grind
  exact eq316104
