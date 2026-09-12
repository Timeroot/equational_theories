import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2061`: `x = ((x ◇ y) ◇ y) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then X else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_pyy_x_pxx_pyx_Equation2061 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 X0 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq10
    | exact resolve eq10 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq61 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq47
    | exact resolve eq47 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq163 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq163 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq188 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq164 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq164
    | (have j0 := eq164 X0 X1
       grind)
    | exact resolve eq164 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq528 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op (M.op X0 X1) X1) X0) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) y) x) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq61 eq63
    | exact resolve eq63 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq532 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq62 eq63
    | exact resolve eq63 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq737 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq186 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1107 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op (M.op (M.op X0 X0) X1) X1) (M.op (M.op X0 X0) X1)) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (M.op (M.op X0 X0) X1) (M.op X0 X0)
       have i₂ := eq171 X0 X1
       grind)
    | exact superpose eq171 eq63
    | (have j1 := eq171 X0 X1
       grind)
    | exact resolve eq63 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq1109 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1107 X0 X1
       have i₂ := eq9 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq1107
    | (have j0 := eq1107 X0 X1
       grind)
    | exact resolve eq1107 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq11437 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq528 X0 X0
       have i₂ := eq9 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq528
    | exact resolve eq528 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11534 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 X0)
       have i₂ := eq11437 X0
       grind)
    | exact superpose eq11437 eq9
    | exact resolve eq9 eq11437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11634 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11534 X0
       have i₂ := eq188 X0 X1
       grind)
    | (have i₁ := eq11534 X1
       have i₂ := eq188 X0 X1
       grind)
    | exact superpose eq188 eq11534
    | (have j1 := eq188 X0 X1
       grind)
    | exact resolve eq11534 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq11675 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11634 X0 X1
       have i₂ := eq11534 X0
       grind)
    | exact superpose eq11534 eq11634
    | (have j0 := eq11634 X0 X1
       grind)
    | exact resolve eq11634 eq11534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11634
  have eq11676 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11675 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11675
  have eq11736 : (M.op x y) = (τ (k (σ y) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq11676 y x
       have i₂ := eq123
       grind)
    | exact superpose eq123 eq11676
    | (have j0 := eq11676 (M.op x y) (τ (k (σ y) (σ x)))
       grind)
    | exact resolve eq11676 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq11887 : (M.op x y) = (τ (k (σ y) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq11736
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11736
    | exact resolve eq11736 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11736
  have eq11902 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq11887 eq11
    | exact resolve eq11 eq11887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11887
  have eq11939 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq20 eq11902
    | exact resolve eq11902 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11902
  have eq11993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11939 eq11676
    | (have j0 := eq11676 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11676 eq11939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11939
  have eq11995 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq11993
    | exact resolve eq11993 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11993
  have eq12023 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11995
       have r₂ := eq27
       grind)
    | exact resolve eq11995 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11995
  have eq12074 : (σ y) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22
       have i₂ := eq12023
       grind)
    | exact superpose eq12023 eq22
    | exact resolve eq22 eq12023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12023
  have eq12138 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12074
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12074
    | exact resolve eq12074 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq12074
  have eq12139 : (σ x) = (σ y) := by grind
  clear eq12138
  have eq12140 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq12139 eq26
    | exact resolve eq26 eq12139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq12141 : x = (τ (σ y)) := by
    first
    | exact superpose eq12139 eq29
    | exact resolve eq29 eq12139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq12163 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq12139 eq532
    | exact resolve eq532 eq12139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq12139
  have eq12169 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq12163
       have i₂ := eq9 sF4 sF3
       grind)
    | exact superpose eq9 eq12163
    | exact resolve eq12163 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12163
  have eq12190 : x = y := by
    first
    | exact superpose eq30 eq12141
    | exact resolve eq12141 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12141
  have eq12192 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq12190
       grind)
    | exact superpose eq12190 eq18
    | exact resolve eq18 eq12190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq12225 : (M.op y (M.op x y)) = (M.op (M.op (M.op (M.op x y) y) y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq530
       have i₂ := eq12190
       grind)
    | exact superpose eq12190 eq530
    | exact resolve eq530 eq12190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq12190
  have eq12227 : (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq12225
       have i₂ := eq9 sF0 y
       grind)
    | exact superpose eq9 eq12225
    | exact resolve eq12225 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12225
  have eq12337 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12140 eq11534
    | exact resolve eq11534 eq12140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12455 : y = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq11534 y
       have i₂ := eq12192
       grind)
    | exact superpose eq12192 eq11534
    | exact resolve eq11534 eq12192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11534
  have eq12479 : (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq12227 eq12
    | (have j0 := eq12 (M.op x y) y
       grind)
    | exact resolve eq12 eq12227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12489 : (M.op x y) ≠ (M.op x y) ∨ (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq12227 eq737
    | (have j0 := eq737 y (M.op x y)
       grind)
    | (have r₁ := eq737 (M.op x y) y
       have r₂ := eq12227
       grind)
    | exact resolve eq737 eq12227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737 eq12227
  have eq12490 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by grind
  clear eq12489
  have eq12491 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq12490
       have i₂ := eq12192
       grind)
    | exact superpose eq12192 eq12490
    | exact resolve eq12490 eq12192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12490
  have eq12676 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq12337 eq528
    | exact resolve eq528 eq12337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq12680 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12169 eq12676
    | exact resolve eq12676 eq12169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12169 eq12676
  have eq12688 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq12680
       have i₂ := eq11437 sF4
       grind)
    | exact superpose eq11437 eq12680
    | exact resolve eq12680 eq11437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12680
  have eq12692 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq12337 eq12688
    | exact resolve eq12688 eq12337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12337 eq12688
  have eq13766 : (M.op x y) = (k (M.op x y) y) := by
    first
    | (have r₁ := eq12491
       have r₂ := eq12479
       grind)
    | exact resolve eq12491 eq12479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12479 eq12491
  have eq13779 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13766 eq40
    | exact resolve eq40 eq13766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq13766
  have eq13784 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq13779
    | exact resolve eq13779 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13779
  have eq13798 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13784
       have i₂ := eq11676 sF1 sF3
       grind)
    | exact superpose eq11676 eq13784
    | (have j1 := eq11676 (σ (M.op x y)) (M.op (σ y) (σ (M.op x y)))
       grind)
    | exact resolve eq13784 eq11676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13784
  have eq14036 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13798 eq9
    | exact resolve eq9 eq13798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14037 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ y) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13798 eq63
    | exact resolve eq63 eq13798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16223 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13798 eq14037
    | exact resolve eq14037 eq13798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13798 eq14037
  have eq16236 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq16223
  have eq16277 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16236 eq14036
    | exact resolve eq14036 eq16236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14036
  have eq16330 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16236 eq11437
    | exact resolve eq11437 eq16236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11437 eq16236
  have eq16340 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq16277
  have eq16408 : (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16330 eq63
    | exact resolve eq63 eq16330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16330
  have eq18144 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16408 eq16340
    | exact resolve eq16340 eq16408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16340 eq16408
  have eq18161 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq18144
  have eq18170 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ y)) (σ y)) (M.op (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18161 eq63
    | exact resolve eq63 eq18161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq18161
  have eq18189 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18170
       have i₂ := eq9 sF1 sF3
       grind)
    | exact superpose eq9 eq18170
    | exact resolve eq18170 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18170
  have eq18192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12140 eq18189
    | exact resolve eq18189 eq12140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18189
  have eq18194 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq18192
       have r₂ := eq27
       grind)
    | exact resolve eq18192 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18192
  have eq18195 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18194 eq27
    | exact resolve eq27 eq18194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq18196 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq18194 eq28
    | exact resolve eq28 eq18194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq18279 : y = (M.op x y) := by
    first
    | exact superpose eq30 eq18196
    | exact resolve eq18196 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq18291 : ∀ X0 : G, (τ (k (σ y) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq116 X0
       have i₂ := eq18279
       grind)
    | exact superpose eq18279 eq116
    | exact resolve eq116 eq18279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq21836 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (M.op X0 y) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1109 y x
       have i₂ := eq12192
       grind)
    | exact superpose eq12192 eq1109
    | (have j0 := eq1109 y X0
       grind)
    | exact resolve eq1109 eq12192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109 eq12192
  have eq22042 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq21836 X0
       have i₂ := eq18279
       grind)
    | exact superpose eq18279 eq21836
    | (have j0 := eq21836 X0
       grind)
    | exact resolve eq21836 eq18279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21836
  have eq22043 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq22042 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22042
  have eq22046 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq22043 X0
       have i₂ := eq18279
       grind)
    | exact superpose eq18279 eq22043
    | (have j0 := eq22043 X0
       grind)
    | exact resolve eq22043 eq18279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22043
  have eq22053 : ∀ X0 : G, (τ (k (σ y) X0)) = (M.op (τ X0) (M.op x y)) ∨ (M.op x y) = (M.op (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq18291 eq22046
    | (have j0 := eq22046 (τ X0)
       grind)
    | exact resolve eq22046 eq18291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18291 eq22046
  have eq24603 : ∀ X0 : G, (M.op x y) ≠ (τ (k (σ y) X0)) ∨ (M.op x y) = (M.op (τ X0) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq22053 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22053
  have eq24746 : ∀ X0 : G, (M.op x y) ≠ (τ (M.op X0 (σ y))) ∨ (M.op x y) = (M.op (τ X0) (M.op x y)) ∨ (σ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24603 x
       have i₂ := eq11676 sF3 x
       grind)
    | exact superpose eq11676 eq24603
    | (have j0 := eq24603 X0
       have j1 := eq11676 (M.op x y) (M.op (τ X0) (M.op x y))
       grind)
    | (have r₁ := eq24603 X0
       have r₂ := eq11676 (M.op x y) (τ (k (σ y) X0))
       grind)
    | (have r₁ := eq24603 X0
       have r₂ := eq11676 (τ (k (σ y) X0)) (M.op x y)
       grind)
    | exact resolve eq24603 eq11676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11676 eq24603
  have eq24979 : (M.op x y) ≠ (τ (σ y)) ∨ (M.op x y) = (M.op (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op x y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12692 eq24746
    | (have j0 := eq24746 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq24746 eq12692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24746
  have eq24989 : (M.op x y) = (M.op (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op x y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq24979
       have r₂ := eq18196
       grind)
    | exact resolve eq24979 eq18196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18196 eq24979
  have eq25032 : (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq24989 eq9
    | exact resolve eq9 eq24989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24989
  have eq25060 : y = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12455 eq25032
    | exact resolve eq25032 eq12455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12455 eq25032
  have eq25073 : (M.op x y) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq25060
       have i₂ := eq18279
       grind)
    | exact superpose eq18279 eq25060
    | exact resolve eq25060 eq18279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18279 eq25060
  have eq25108 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq25073 eq11
    | exact resolve eq11 eq25073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25073
  have eq25143 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq25108
    | exact resolve eq25108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq25108
  have eq25148 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq18194 eq25143
    | exact resolve eq25143 eq18194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18194 eq25143
  have eq25149 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq25148
  have eq25176 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq25149 eq12692
    | exact resolve eq12692 eq25149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12692 eq25149
  have eq25239 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12140 eq25176
    | exact resolve eq25176 eq12140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12140 eq25176
  have eq25249 : False := by grind
  exact eq25249
