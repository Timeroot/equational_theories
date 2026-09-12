import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_y_pyy_x_pyx_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, x = (M.op (M.op (M.op x X0) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq44
    | exact resolve eq44 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq50
    | exact resolve eq50 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq100 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq101 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq105 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq101
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq101
    | exact resolve eq101 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq107 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq105
    | exact resolve eq105 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq105
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq100
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq109
    | exact resolve eq109 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21 eq115
    | exact resolve eq115 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq116
    | exact resolve eq116 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq145 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq107
       grind)
    | exact superpose eq107 eq16
    | exact resolve eq16 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq236 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) x) X1) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq256 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X1) (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq498 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) X2)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq500 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) X2)) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq517 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1177 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq517 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq517
    | (have j0 := eq517 x y X0
       grind)
    | exact resolve eq517 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1178 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq517
    | (have j0 := eq517 (σ x) (σ y) X0
       grind)
    | exact resolve eq517 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1196 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq517 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq517
    | (have j0 := eq517 x X0 y
       grind)
    | exact resolve eq517 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1197 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq517
    | (have j0 := eq517 (σ x) X0 (σ y)
       grind)
    | exact resolve eq517 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1202 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq517 X0 X1 x
       grind)
    | exact superpose eq517 eq14
    | exact resolve eq14 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1294 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1202 (σ X0) X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq1202
    | exact resolve eq1202 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1300 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1202 X0 (M.op X0 X1)
       have i₂ := eq517 X0 X0 X1
       grind)
    | exact superpose eq517 eq1202
    | exact resolve eq1202 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1305 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1 X1 X0
       have i₂ := eq1202 (M.op X0 X1) X0
       grind)
    | exact superpose eq1202 eq56
    | exact resolve eq56 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1314 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq1202 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1202 eq14
    | exact resolve eq14 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1332 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1305 X0 X1
       have i₂ := eq517 X0 X1 X1
       grind)
    | exact superpose eq517 eq1305
    | exact resolve eq1305 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1429 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1196 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1196
    | (have j0 := eq1196 y
       grind)
    | exact resolve eq1196 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1469 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1429
       have i₂ := eq1177 X0
       grind)
    | exact superpose eq1177 eq1429
    | exact resolve eq1429 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1631 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq27 eq1197
    | (have j0 := eq1197 (σ y)
       grind)
    | exact resolve eq1197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1671 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1178 eq1631
    | exact resolve eq1631 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2004 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq236 eq1300
    | exact resolve eq1300 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2005 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1300 (M.op x x) y
       have i₂ := eq1429
       grind)
    | exact superpose eq1429 eq1300
    | exact resolve eq1300 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq2010 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq243 eq1300
    | exact resolve eq1300 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2011 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1631 eq1300
    | exact resolve eq1300 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631
  have eq2043 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2011
       have i₂ := eq1202 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq1202 eq2011
    | exact resolve eq2011 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011
  have eq2044 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq2010
       have i₂ := eq1202 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1202 eq2010
    | exact resolve eq2010 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq2049 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2005
       have i₂ := eq1202 x (M.op x x)
       grind)
    | exact superpose eq1202 eq2005
    | exact resolve eq2005 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005
  have eq2050 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2004
       have i₂ := eq1202 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1202 eq2004
    | exact resolve eq2004 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202 eq2004
  have eq2097 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq2044 eq243
    | exact resolve eq243 eq2044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2105 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2044 eq517
    | exact resolve eq517 eq2044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2124 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2105 x
       have i₂ := eq517 sF4 sF2 x
       grind)
    | exact superpose eq517 eq2105
    | exact resolve eq2105 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105
  have eq2130 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq2044 eq2124
    | exact resolve eq2124 eq2044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124
  have eq2195 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq2050 eq236
    | exact resolve eq236 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2204 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2050 eq517
    | exact resolve eq517 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2224 : (M.op (M.op (M.op x y) (M.op x y)) x) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq2204 x
       have i₂ := eq517 sF0 x x
       grind)
    | exact superpose eq517 eq2204
    | exact resolve eq2204 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204
  have eq2230 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq2050 eq2224
    | exact resolve eq2224 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224
  have eq2409 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq2044 eq2043
    | exact resolve eq2043 eq2044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043
  have eq2410 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq2050 eq2049
    | exact resolve eq2049 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049
  have eq3168 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq1332 x X0
       have i₂ := eq1196 X0
       grind)
    | exact superpose eq1196 eq1332
    | exact resolve eq1332 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3169 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq1197 eq1332
    | exact resolve eq1332 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3170 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1332 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1332
    | exact resolve eq1332 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3171 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq236 eq1332
    | exact resolve eq1332 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3172 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq243 eq1332
    | exact resolve eq1332 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3179 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1332 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1300 X0 X1
       grind)
    | exact superpose eq1300 eq1332
    | exact resolve eq1332 eq1300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3252 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3179 X0 X1
       have i₂ := eq1314 X0 X0
       grind)
    | exact superpose eq1314 eq3179
    | exact resolve eq3179 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314 eq3179
  have eq3261 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3252 X0 X1
       have i₂ := eq517 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq517 eq3252
    | exact resolve eq3252 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3252
  have eq3262 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3261 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq3261
    | exact resolve eq3261 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3261
  have eq3271 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) x) = (M.op (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq3171 eq517
    | exact resolve eq517 eq3171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3274 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) y) X0) := by
    intro X0
    first
    | (have i₁ := eq3271 X0
       have i₂ := eq517 sF0 y y
       grind)
    | exact superpose eq517 eq3271
    | exact resolve eq3271 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3271
  have eq3279 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) y) X0) x) := by
    intro X0
    first
    | exact superpose eq236 eq3274
    | exact resolve eq3274 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq3274
  have eq3292 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq3172 eq517
    | exact resolve eq517 eq3172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3295 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq3292 X0
       have i₂ := eq517 sF4 sF3 sF3
       grind)
    | exact superpose eq517 eq3292
    | exact resolve eq3292 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3292
  have eq3300 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq243 eq3295
    | exact resolve eq3295 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq3295
  have eq4320 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1469 eq239
    | (have j0 := eq239 y X1
       grind)
    | exact resolve eq239 eq1469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq4321 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq2050 eq4320
    | exact resolve eq4320 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4320
  have eq4513 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3170 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq3170 X0 X1
       grind)
    | exact superpose eq3170 eq3170
    | exact resolve eq3170 eq3170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4521 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq4321 eq3170
    | exact resolve eq3170 eq4321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4321
  have eq4526 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq3171 eq3170
    | exact resolve eq3170 eq3171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4537 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq3172 eq3170
    | exact resolve eq3170 eq3172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4572 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3262 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq3170 X0 X1
       grind)
    | exact superpose eq3170 eq3262
    | exact resolve eq3262 eq3170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3262
  have eq4573 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4572 X0 X1
       have i₂ := eq517 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq517 eq4572
    | exact resolve eq4572 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4572
  have eq4592 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq4537
       have i₂ := eq1332 sF2 sF4
       grind)
    | exact superpose eq1332 eq4537
    | exact resolve eq4537 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4537
  have eq4600 : (M.op (M.op x y) y) = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq4526
       have i₂ := eq1332 x sF0
       grind)
    | exact superpose eq1332 eq4526
    | exact resolve eq4526 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4526
  have eq4603 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq2195 eq4521
    | exact resolve eq4521 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195 eq4521
  have eq4610 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4513 X0 X1
       have i₂ := eq1332 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1332 eq4513
    | exact resolve eq4513 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4513
  have eq4633 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4573 X0 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq4573
    | exact resolve eq4573 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4573
  have eq4646 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1197 eq4592
    | exact resolve eq4592 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197 eq4592
  have eq4650 : (M.op (M.op x y) y) = (M.op (M.op x x) x) := by
    first
    | exact superpose eq1196 eq4600
    | exact resolve eq4600 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196 eq4600
  have eq4651 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq2410 eq4603
    | exact resolve eq4603 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410 eq4603
  have eq4656 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4610 X0 X1
       have i₂ := eq517 X0 X0 X1
       grind)
    | exact superpose eq517 eq4610
    | exact resolve eq4610 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4610
  have eq5017 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1671 eq246
    | (have j0 := eq246 (σ y) X1
       grind)
    | exact resolve eq246 eq1671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq5018 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq2044 eq5017
    | exact resolve eq5017 eq2044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5017
  have eq5118 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq5018 eq3170
    | exact resolve eq3170 eq5018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5018
  have eq5124 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq2097 eq5118
    | exact resolve eq5118 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097 eq5118
  have eq5132 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq2409 eq5124
    | exact resolve eq5124 eq2409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409 eq5124
  have eq5177 : ∀ X0 X1 : G, (M.op (M.op x X0) x) = (M.op (M.op (M.op (M.op (M.op x X0) x) X1) x) X1) := by
    intro X0 X1
    first
    | exact superpose eq3168 eq252
    | exact resolve eq252 eq3168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq3168
  have eq5220 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq3169 eq256
    | exact resolve eq256 eq3169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq3169
  have eq6490 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op (M.op (M.op x y) y) X0) x) X0) := by
    intro X0
    first
    | (have i₁ := eq5177 x x
       have i₂ := eq4650
       grind)
    | exact superpose eq4650 eq5177
    | exact resolve eq5177 eq4650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4650 eq5177
  have eq6542 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | exact superpose eq3279 eq6490
    | exact resolve eq6490 eq3279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3279 eq6490
  have eq7007 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq4646 eq5220
    | exact resolve eq5220 eq4646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4646 eq5220
  have eq7059 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq3300 eq7007
    | exact resolve eq7007 eq3300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3300 eq7007
  have eq7356 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4656 X0 X2
       have i₂ := eq4656 X0 X1
       grind)
    | (have i₁ := eq4656 X1 X1
       have i₂ := eq4656 X1 X1
       grind)
    | exact superpose eq4656 eq4656
    | exact resolve eq4656 eq4656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7426 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1300 X0 X2
       have i₂ := eq4656 X0 X1
       grind)
    | (have i₁ := eq1300 X1 X1
       have i₂ := eq4656 X1 X1
       grind)
    | exact superpose eq4656 eq1300
    | exact resolve eq1300 eq4656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4656
  have eq13567 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1469 eq498
    | (have j0 := eq498 y X1 X2
       grind)
    | exact resolve eq498 eq1469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq1469
  have eq13568 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq2050 eq13567
    | exact resolve eq13567 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2050 eq13567
  have eq13569 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq4651 eq13568
    | exact resolve eq13568 eq4651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4651 eq13568
  have eq13584 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq13569 y
       have i₂ := eq1177 X0
       grind)
    | exact superpose eq1177 eq13569
    | exact resolve eq13569 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177 eq13569
  have eq13624 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq13584 x
       have i₂ := eq517 sF0 x (M.op x x)
       grind)
    | exact superpose eq517 eq13584
    | exact resolve eq13584 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13584
  have eq13646 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq13624
       have i₂ := eq1332 sF0 x
       grind)
    | exact superpose eq1332 eq13624
    | exact resolve eq13624 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13624
  have eq13662 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq2230 eq13646
    | exact resolve eq13646 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230 eq13646
  have eq13682 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq13662
       have i₂ := eq7356 sF0 x x
       grind)
    | (have i₁ := eq13662
       have i₂ := eq7356 sF0 x x
       grind)
    | exact superpose eq7356 eq13662
    | exact resolve eq13662 eq7356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13662
  have eq13733 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1671 eq500
    | (have j0 := eq500 (σ y) X1 X2
       grind)
    | exact resolve eq500 eq1671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq1671
  have eq13734 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq2044 eq13733
    | exact resolve eq13733 eq2044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2044 eq13733
  have eq13735 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ x)) X2)) (σ y)) := by
    intro X2
    first
    | exact superpose eq5132 eq13734
    | exact resolve eq13734 eq5132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5132 eq13734
  have eq13750 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq1178 eq13735
    | exact resolve eq13735 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178 eq13735
  have eq13790 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq13750 x
       have i₂ := eq517 sF4 sF2 (M.op sF2 x)
       grind)
    | exact superpose eq517 eq13750
    | exact resolve eq13750 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq13750
  have eq13812 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq13790
       have i₂ := eq1332 sF4 sF2
       grind)
    | exact superpose eq1332 eq13790
    | exact resolve eq13790 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332 eq13790
  have eq13828 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (σ y)) := by
    first
    | exact superpose eq2130 eq13812
    | exact resolve eq13812 eq2130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130 eq13812
  have eq13848 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13828
       have i₂ := eq7356 sF4 sF2 x
       grind)
    | (have i₁ := eq13828
       have i₂ := eq7356 sF4 x sF2
       grind)
    | exact superpose eq7356 eq13828
    | exact resolve eq13828 eq7356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7356 eq13828
  have eq64471 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq64479 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq64471
    | exact resolve eq64471 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64471
  have eq64490 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq64479
       have r₂ := eq28
       grind)
    | exact resolve eq64479 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64479
  have eq64494 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq64490
    | exact resolve eq64490 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64490
  have eq64582 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq64494 eq1300
    | exact resolve eq1300 eq64494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300 eq64494
  have eq64607 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3172 eq64582
    | exact resolve eq64582 eq3172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3172 eq64582
  have eq64639 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq64607 eq145
    | exact resolve eq145 eq64607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq64607
  have eq64789 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq64639
    | exact resolve eq64639 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64639
  have eq64790 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq64789
  have eq65248 : y = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3170 y y
       have i₂ := eq64790
       grind)
    | exact superpose eq64790 eq3170
    | exact resolve eq3170 eq64790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3170 eq64790
  have eq65271 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3171 eq65248
    | exact resolve eq65248 eq3171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3171 eq65248
  have eq65356 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1294 y X0
       have i₂ := eq65271
       grind)
    | exact superpose eq65271 eq1294
    | exact resolve eq1294 eq65271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294
  have eq65411 : y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4633 y y
       have i₂ := eq65271
       grind)
    | exact superpose eq65271 eq4633
    | exact resolve eq4633 eq65271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4633 eq65271
  have eq65439 : y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq65411
       have i₂ := eq6542 y
       grind)
    | (have i₁ := eq65411
       have i₂ := eq6542 x
       grind)
    | exact superpose eq6542 eq65411
    | exact resolve eq65411 eq6542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6542 eq65411
  have eq65461 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq65356 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq65356
    | (have j0 := eq65356 X0
       grind)
    | exact resolve eq65356 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65356
  have eq65489 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7059 eq65461
    | (have j0 := eq65461 (σ y)
       grind)
    | exact resolve eq65461 eq7059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7059 eq65461
  have eq65508 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq65489
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq65489
    | exact resolve eq65489 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65489
  have eq66524 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) X0) y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq65439 eq7426
    | exact resolve eq7426 eq65439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65439
  have eq66540 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13682 eq66524
    | exact resolve eq66524 eq13682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13682 eq66524
  have eq67078 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq65508 eq7426
    | exact resolve eq7426 eq65508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7426 eq65508
  have eq67094 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13848 eq67078
    | exact resolve eq67078 eq13848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13848 eq67078
  have eq67917 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq66540
       grind)
    | exact superpose eq66540 eq73
    | exact resolve eq73 eq66540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq66540
  have eq68121 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq67917
    | exact resolve eq67917 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67917
  have eq70662 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq68121 eq67094
    | exact resolve eq67094 eq68121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67094 eq68121
  have eq70783 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq70662
  have eq70813 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq70783
       have r₂ := eq28
       grind)
    | exact resolve eq70783 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70783
  have eq70840 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq70813 eq30
    | exact resolve eq30 eq70813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq70813
  have eq71022 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq70840
    | exact resolve eq70840 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq70840
  have eq71023 : x = y := by grind
  clear eq71022
  have eq71061 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq71023
       grind)
    | exact superpose eq71023 eq19
    | exact resolve eq19 eq71023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq71062 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq71023
       grind)
    | exact superpose eq71023 eq25
    | exact resolve eq25 eq71023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq71023
  have eq71247 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq71062
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq71062
    | exact resolve eq71062 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq71062
  have eq71288 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq71247 eq27
    | exact resolve eq27 eq71247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq71247
  have eq71796 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq71288 eq72
    | exact resolve eq72 eq71288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq71288
  have eq72009 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq71796
       have i₂ := eq71061
       grind)
    | exact superpose eq71061 eq71796
    | exact resolve eq71796 eq71061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71061 eq71796
  have eq72052 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72009 eq15
    | exact resolve eq15 eq72009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72009
  have eq72148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq72052
    | exact resolve eq72052 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq72052
  have eq72175 : False := by grind
  exact eq72175

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pyy_pyx_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : (σ (k x (k x x))) = (k (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq36 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq36
    | exact resolve eq36 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq84 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq91 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq84
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq85
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq93
    | exact resolve eq93 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq209 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) X2)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq499 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) X2)) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq506 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X5)) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3 X2 X3
       have i₂ := eq56 X0 X1 X2 X3
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq906 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq515 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq515
    | (have j0 := eq515 x y X0
       grind)
    | exact resolve eq515 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq907 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq515
    | (have j0 := eq515 (σ x) (σ y) X0
       grind)
    | exact resolve eq515 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq919 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq515 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq515
    | (have j0 := eq515 x X0 y
       grind)
    | exact resolve eq515 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq515
    | (have j0 := eq515 (σ x) X0 (σ y)
       grind)
    | exact resolve eq515 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq924 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq515 X0 X1 x
       grind)
    | exact superpose eq515 eq14
    | exact resolve eq14 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq985 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq924 X0 (M.op X0 X1)
       have i₂ := eq515 X0 X0 X1
       grind)
    | exact superpose eq515 eq924
    | exact resolve eq924 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq990 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1 X1 X0
       have i₂ := eq924 (M.op X0 X1) X0
       grind)
    | exact superpose eq924 eq56
    | exact resolve eq56 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq995 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq924 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq924 eq14
    | exact resolve eq14 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1011 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq990 X0 X1
       have i₂ := eq515 X0 X1 X1
       grind)
    | exact superpose eq515 eq990
    | exact resolve eq990 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1102 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq919 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq919
    | (have j0 := eq919 y
       grind)
    | exact resolve eq919 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1181 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1102
       have i₂ := eq906 X0
       grind)
    | exact superpose eq906 eq1102
    | exact resolve eq1102 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1271 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq27 eq920
    | (have j0 := eq920 (σ y)
       grind)
    | exact resolve eq920 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1307 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq907 eq1271
    | exact resolve eq1271 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1457 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq985 (M.op x x) y
       have i₂ := eq1102
       grind)
    | exact superpose eq1102 eq985
    | exact resolve eq985 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1461 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq209 eq985
    | exact resolve eq985 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1463 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1271 eq985
    | exact resolve eq985 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq1467 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq216 eq985
    | exact resolve eq985 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1493 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1467
       have i₂ := eq924 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq924 eq1467
    | exact resolve eq1467 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq1497 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1463
       have i₂ := eq924 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq924 eq1463
    | exact resolve eq1463 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463
  have eq1499 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1461
       have i₂ := eq924 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq924 eq1461
    | exact resolve eq1461 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461
  have eq1503 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1457
       have i₂ := eq924 x (M.op x x)
       grind)
    | exact superpose eq924 eq1457
    | exact resolve eq1457 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457
  have eq1534 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1493 eq216
    | exact resolve eq216 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1542 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1493 eq515
    | exact resolve eq515 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1551 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq1542 x
       have i₂ := eq515 sF4 sF2 x
       grind)
    | exact superpose eq515 eq1542
    | exact resolve eq1542 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq1554 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq1493 eq1551
    | exact resolve eq1551 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq1557 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1499 eq209
    | exact resolve eq209 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1565 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1499 eq515
    | exact resolve eq515 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1574 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq1565 x
       have i₂ := eq515 sF0 x x
       grind)
    | exact superpose eq515 eq1565
    | exact resolve eq1565 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq1577 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq1499 eq1574
    | exact resolve eq1574 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574
  have eq1708 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq1493 eq1497
    | exact resolve eq1497 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq1709 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1499 eq1503
    | exact resolve eq1503 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503
  have eq2306 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1011 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1011
    | exact resolve eq1011 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2308 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq209 eq1011
    | exact resolve eq1011 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2310 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq216 eq1011
    | exact resolve eq1011 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2314 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1011 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq985 X0 X1
       grind)
    | exact superpose eq985 eq1011
    | exact resolve eq1011 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2390 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2314 X0 X1
       have i₂ := eq995 X0 X0
       grind)
    | exact superpose eq995 eq2314
    | exact resolve eq2314 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2314
  have eq2396 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2390 X0 X1
       have i₂ := eq515 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq515 eq2390
    | exact resolve eq2390 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2390
  have eq2397 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2396 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2396
    | exact resolve eq2396 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2396
  have eq2513 : x ≠ (M.op x y) ∨ (k (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq2308 eq13
    | (have j0 := eq13 (M.op x y) (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq2308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2527 : (M.op (M.op (M.op x y) (M.op x y)) y) = (k (M.op x y) (M.op (M.op x y) y)) ∨ x ≠ (M.op x y) := by
    first
    | (have i₁ := eq2513
       have i₂ := eq515 sF0 y y
       grind)
    | exact superpose eq515 eq2513
    | exact resolve eq2513 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2513
  have eq2531 : x ≠ (M.op x y) ∨ x = (k (M.op x y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq209 eq2527
    | exact resolve eq2527 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527
  have eq2809 : (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq2308 eq2397
    | exact resolve eq2397 eq2308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2818 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq2310 eq2397
    | exact resolve eq2397 eq2310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2822 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2397 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2397
    | (have j0 := eq2397 x y
       grind)
    | exact resolve eq2397 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2881 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq2818
       have i₂ := eq515 sF4 sF3 sF3
       grind)
    | exact superpose eq515 eq2818
    | exact resolve eq2818 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2818
  have eq2890 : (M.op (M.op (M.op x y) (M.op x y)) y) = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq2809
       have i₂ := eq515 sF0 y y
       grind)
    | exact superpose eq515 eq2809
    | exact resolve eq2809 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2809
  have eq2916 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq216 eq2881
    | exact resolve eq2881 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2881
  have eq2924 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq209 eq2890
    | exact resolve eq2890 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890
  have eq3111 : (σ x) ≠ (σ x) ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq2916 eq13
    | (have j0 := eq13 (σ x) (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq13 (σ x) (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq2916
       grind)
    | exact resolve eq13 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3123 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by grind
  clear eq3111
  have eq3130 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq3123
       have i₂ := eq515 sF4 sF3 sF3
       grind)
    | exact superpose eq515 eq3123
    | exact resolve eq3123 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3123
  have eq3135 : (σ x) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq216 eq3130
    | exact resolve eq3130 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3130
  have eq3406 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1181 eq212
    | (have j0 := eq212 y X1
       grind)
    | exact resolve eq212 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq3407 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq1499 eq3406
    | exact resolve eq3406 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406
  have eq3695 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1307 eq219
    | (have j0 := eq219 (σ y) X1
       grind)
    | exact resolve eq219 eq1307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq3696 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1493 eq3695
    | exact resolve eq3695 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3695
  have eq3721 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2306 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2306 X0 X1
       grind)
    | exact superpose eq2306 eq2306
    | exact resolve eq2306 eq2306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3727 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq3407 eq2306
    | exact resolve eq2306 eq3407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3407
  have eq3736 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq2308 eq2306
    | exact resolve eq2306 eq2308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2308
  have eq3748 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2310 eq2306
    | exact resolve eq2306 eq2310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310
  have eq3785 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2397 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2306 X0 X1
       grind)
    | exact superpose eq2306 eq2397
    | exact resolve eq2397 eq2306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3786 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3785 X0 X1
       have i₂ := eq515 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq515 eq3785
    | exact resolve eq3785 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3785
  have eq3808 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq3748
       have i₂ := eq1011 sF2 sF4
       grind)
    | exact superpose eq1011 eq3748
    | exact resolve eq3748 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3748
  have eq3817 : (M.op (M.op x y) y) = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq3736
       have i₂ := eq1011 x sF0
       grind)
    | exact superpose eq1011 eq3736
    | exact resolve eq3736 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3736
  have eq3825 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq1557 eq3727
    | exact resolve eq3727 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557 eq3727
  have eq3829 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3721 X0 X1
       have i₂ := eq1011 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1011 eq3721
    | exact resolve eq3721 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3721
  have eq3844 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3786 X0 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq3786
    | exact resolve eq3786 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3786
  have eq3859 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq920 eq3808
    | exact resolve eq3808 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq3808
  have eq3864 : (M.op (M.op x y) y) = (M.op (M.op x x) x) := by
    first
    | exact superpose eq919 eq3817
    | exact resolve eq3817 eq919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919 eq3817
  have eq3868 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq1709 eq3825
    | exact resolve eq3825 eq1709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1709 eq3825
  have eq3870 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3829 X0 X1
       have i₂ := eq515 X0 X0 X1
       grind)
    | exact superpose eq515 eq3829
    | exact resolve eq3829 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3829
  have eq4130 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq3696 eq2306
    | exact resolve eq2306 eq3696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3696
  have eq4136 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq1534 eq4130
    | exact resolve eq4130 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534 eq4130
  have eq4144 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1708 eq4136
    | exact resolve eq4136 eq1708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708 eq4136
  have eq5487 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq79 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq79
    | (have j0 := eq79 x
       grind)
    | exact resolve eq79 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq5517 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5487
  have eq5524 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5517
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5517
    | exact resolve eq5517 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5517
  have eq5537 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5524
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5524 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5524
  have eq5542 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5537 eq50
    | exact resolve eq50 eq5537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq6538 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3870 X0 X2
       have i₂ := eq3870 X0 X1
       grind)
    | (have i₁ := eq3870 X1 X1
       have i₂ := eq3870 X1 X1
       grind)
    | exact superpose eq3870 eq3870
    | exact resolve eq3870 eq3870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6542 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq3870 x X0
       have i₂ := eq3864
       grind)
    | exact superpose eq3864 eq3870
    | exact resolve eq3870 eq3864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3864
  have eq6543 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq3859 eq3870
    | exact resolve eq3870 eq3859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3859
  have eq6594 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq985 X0 X2
       have i₂ := eq3870 X0 X1
       grind)
    | (have i₁ := eq985 X1 X1
       have i₂ := eq3870 X1 X1
       grind)
    | exact superpose eq3870 eq985
    | exact resolve eq985 eq3870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985 eq3870
  have eq8122 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1181 eq498
    | (have j0 := eq498 y X1 X2
       grind)
    | exact resolve eq498 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq1181
  have eq8123 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1499 eq8122
    | exact resolve eq8122 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8122
  have eq8124 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq3868 eq8123
    | exact resolve eq8123 eq3868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3868 eq8123
  have eq8274 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq8124 y
       have i₂ := eq906 X0
       grind)
    | exact superpose eq906 eq8124
    | exact resolve eq8124 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906 eq8124
  have eq8312 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq8274 x
       have i₂ := eq515 sF0 x (M.op x x)
       grind)
    | exact superpose eq515 eq8274
    | exact resolve eq8274 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8274
  have eq8328 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq8312
       have i₂ := eq1011 sF0 x
       grind)
    | exact superpose eq1011 eq8312
    | exact resolve eq8312 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8312
  have eq8340 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq1577 eq8328
    | exact resolve eq8328 eq1577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1577 eq8328
  have eq8391 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1307 eq499
    | (have j0 := eq499 (σ y) X1 X2
       grind)
    | exact resolve eq499 eq1307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499 eq1307
  have eq8392 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1493 eq8391
    | exact resolve eq8391 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493 eq8391
  have eq8393 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ x)) X2)) (σ y)) := by
    intro X2
    first
    | exact superpose eq4144 eq8392
    | exact resolve eq8392 eq4144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4144 eq8392
  have eq8398 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq907 eq8393
    | exact resolve eq8393 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907 eq8393
  have eq8436 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq8398 x
       have i₂ := eq515 sF4 sF2 (M.op sF2 x)
       grind)
    | exact superpose eq515 eq8398
    | exact resolve eq8398 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8398
  have eq8452 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq8436
       have i₂ := eq1011 sF4 sF2
       grind)
    | exact superpose eq1011 eq8436
    | exact resolve eq8436 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011 eq8436
  have eq8464 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1554 eq8452
    | exact resolve eq8452 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554 eq8452
  have eq9656 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) y) X0) X0) := by
    intro X0
    first
    | exact superpose eq2924 eq6538
    | exact resolve eq6538 eq2924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2924
  have eq9978 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq8340
       have i₂ := eq6538 sF0 x x
       grind)
    | (have i₁ := eq8340
       have i₂ := eq6538 sF0 x x
       grind)
    | exact superpose eq6538 eq8340
    | exact resolve eq8340 eq6538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8340
  have eq9998 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8464
       have i₂ := eq6538 sF4 sF2 x
       grind)
    | (have i₁ := eq8464
       have i₂ := eq6538 sF4 x sF2
       grind)
    | exact superpose eq6538 eq8464
    | exact resolve eq8464 eq6538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6538 eq8464
  have eq16405 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X3) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq506 X0 X1 x X3 X4
       have i₂ := eq515 X0 X1 x
       grind)
    | exact superpose eq515 eq506
    | exact resolve eq506 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq16510 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op X0 X0) (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16405 X0 (M.op X0 X1) X2 X2
       have i₂ := eq56 X0 X0 X1 X2
       grind)
    | exact superpose eq56 eq16405
    | exact resolve eq16405 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq16405
  have eq16612 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16510 X0 X1 X2
       have i₂ := eq515 (M.op X0 X0) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq515 eq16510
    | exact resolve eq16510 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16510
  have eq16720 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16612 X0 X1 X2
       have i₂ := eq515 X0 X0 X0
       grind)
    | exact superpose eq515 eq16612
    | exact resolve eq16612 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16612
  have eq16791 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16720 X0 X1 X2
       have i₂ := eq6594 X0 X0 X1
       grind)
    | exact superpose eq6594 eq16720
    | exact resolve eq16720 eq6594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16720
  have eq16830 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) X0) X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq16791 X0 x X2
       have i₂ := eq515 X0 X0 x
       grind)
    | exact superpose eq515 eq16791
    | exact resolve eq16791 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16791
  have eq25751 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X5)) X3) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq652 X0 X1 x X3 X4 X5
       have i₂ := eq515 X0 X1 x
       grind)
    | exact superpose eq515 eq652
    | exact resolve eq652 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq31991 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5537 eq91
    | exact resolve eq91 eq5537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq37445 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25751 X0 X0 X1 X2 X0
       have i₂ := eq16830 X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2)
       grind)
    | exact superpose eq16830 eq25751
    | exact resolve eq25751 eq16830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25751
  have eq37487 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X0 X1) X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37445 X0 X2 X2
       have i₂ := eq16830 X0 X2
       grind)
    | exact superpose eq16830 eq37445
    | exact resolve eq37445 eq16830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16830 eq37445
  have eq37567 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37487 X0 X1 X2
       have i₂ := eq14 X0 X1 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq14 eq37487
    | exact resolve eq37487 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37487
  have eq39077 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq31991
       grind)
    | exact superpose eq31991 eq16
    | exact resolve eq16 eq31991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31991
  have eq39149 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5542 eq39077
    | exact resolve eq39077 eq5542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39077
  have eq39167 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq39149
       have r₂ := eq13 x x
       grind)
    | exact resolve eq39149 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39149
  have eq39171 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq39167
       grind)
    | exact superpose eq39167 eq44
    | exact resolve eq44 eq39167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq39172 : (k (σ x) (k (σ x) (σ x))) = (σ (k x (M.op x x))) := by
    first
    | (have i₁ := eq47
       have i₂ := eq39167
       grind)
    | exact superpose eq39167 eq47
    | exact resolve eq47 eq39167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq39205 : (σ (k x (M.op x x))) = (k (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5537 eq39172
    | exact resolve eq39172 eq5537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39172
  have eq39206 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq5537 eq39171
    | exact resolve eq39171 eq5537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5537 eq39171
  have eq45711 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (k (M.op (M.op X0 X0) X0) X0) ∨ (M.op (M.op X0 X0) X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq37567
  have eq45793 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) X0) X0) ∨ (M.op (M.op X0 X0) X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq45711 X0
       have i₂ := eq995 X0 X0
       grind)
    | exact superpose eq995 eq45711
    | (have j0 := eq45711 X0
       grind)
    | exact resolve eq45711 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995 eq45711
  have eq46057 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have j0 := eq45793 X0
       have j1 := eq13 (M.op (M.op X0 X0) X0) X0
       grind)
    | (have r₁ := eq45793 x
       have r₂ := eq13 (M.op (M.op x x) x) x
       grind)
    | exact resolve eq45793 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45793
  have eq46458 : (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (k (M.op x x) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq9656 eq46057
    | exact resolve eq46057 eq9656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9656
  have eq46463 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46057 (M.op X0 X0)
       have i₂ := eq924 X0 (M.op X0 X0)
       grind)
    | exact superpose eq924 eq46057
    | exact resolve eq46057 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924 eq46057
  have eq46497 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46463 X0
       have i₂ := eq515 X0 X0 X0
       grind)
    | exact superpose eq515 eq46463
    | exact resolve eq46463 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46463
  have eq46500 : (M.op (M.op (M.op x y) (M.op x y)) y) = (k (M.op x x) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq46458
       have i₂ := eq515 sF0 y y
       grind)
    | exact superpose eq515 eq46458
    | exact resolve eq46458 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46458
  have eq46510 : x = (k (M.op x x) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq209 eq46500
    | exact resolve eq46500 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq46500
  have eq47416 : (k (σ x) (M.op (σ x) (σ x))) = (σ (M.op (M.op x x) x)) := by
    first
    | (have i₁ := eq39205
       have i₂ := eq46497 x
       grind)
    | exact superpose eq46497 eq39205
    | exact resolve eq39205 eq46497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39205
  have eq47448 : (σ (M.op (M.op x y) y)) = (k (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq47416
       have i₂ := eq6542 x
       grind)
    | exact superpose eq6542 eq47416
    | exact resolve eq47416 eq6542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47416
  have eq47455 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq47448
       have i₂ := eq46497 sF2
       grind)
    | exact superpose eq46497 eq47448
    | exact resolve eq47448 eq46497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46497 eq47448
  have eq47457 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq6543 eq47455
    | exact resolve eq47455 eq6543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47455
  have eq51805 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq94 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq51805
    | exact resolve eq51805 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51805
  have eq51824 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq51813
       have r₂ := eq28
       grind)
    | exact resolve eq51813 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51813
  have eq51838 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq51824 eq5542
    | exact resolve eq5542 eq51824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5542 eq51824
  have eq51964 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq51838
       have i₂ := eq39167
       grind)
    | exact superpose eq39167 eq51838
    | exact resolve eq51838 eq39167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51838
  have eq51977 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq51964
    | exact resolve eq51964 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq51964
  have eq51978 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq51977
  have eq51994 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq51978 eq2306
    | exact resolve eq2306 eq51978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51978
  have eq52013 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq6543 eq51994
    | exact resolve eq51994 eq6543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6543 eq51994
  have eq52023 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq52013 eq3135
    | exact resolve eq3135 eq52013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3135
  have eq53328 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq52023 eq94
    | exact resolve eq94 eq52023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq52023
  have eq53343 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by grind
  clear eq53328
  have eq53825 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2397 x x
       have i₂ := eq53343
       grind)
    | exact superpose eq53343 eq2397
    | exact resolve eq2397 eq53343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53343
  have eq53842 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53825
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53825
    | exact resolve eq53825 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53825
  have eq53886 : y = (M.op (M.op x x) x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2306 y x
       have i₂ := eq53842
       grind)
    | exact superpose eq53842 eq2306
    | exact resolve eq2306 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2306 eq53842
  have eq53905 : y = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53886
       have i₂ := eq6542 x
       grind)
    | exact superpose eq6542 eq53886
    | exact resolve eq53886 eq6542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6542 eq53886
  have eq54312 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53905 eq47457
    | exact resolve eq47457 eq53905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54346 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) X0) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq53905 eq6594
    | exact resolve eq6594 eq53905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53905
  have eq54358 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9978 eq54346
    | exact resolve eq54346 eq9978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54346
  have eq54377 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq54312
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq54312
    | exact resolve eq54312 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54312
  have eq54780 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39206
       have i₂ := eq54358
       grind)
    | exact superpose eq54358 eq39206
    | exact resolve eq39206 eq54358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54358
  have eq54907 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq54780
    | exact resolve eq54780 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54780
  have eq55133 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq54377 eq6594
    | exact resolve eq6594 eq54377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6594 eq54377
  have eq55145 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9998 eq55133
    | exact resolve eq55133 eq9998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9998 eq55133
  have eq56650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55145 eq54907
    | exact resolve eq54907 eq55145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54907 eq55145
  have eq56732 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq56650
  have eq56771 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq56732
       have r₂ := eq28
       grind)
    | exact resolve eq56732 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56732
  have eq56822 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56771 eq29
    | exact resolve eq29 eq56771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq56771
  have eq57037 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq56822
    | exact resolve eq56822 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq56822
  have eq57113 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57037 eq21
    | exact resolve eq21 eq57037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57190 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57037 eq2822
    | exact resolve eq2822 eq57037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822
  have eq57229 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y X0) X0) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq57037 eq9978
    | exact resolve eq9978 eq57037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9978 eq57037
  have eq57285 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57229 x
       have i₂ := eq3844 y x
       grind)
    | exact superpose eq3844 eq57229
    | exact resolve eq57229 eq3844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57229
  have eq57290 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57190
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57190
    | exact resolve eq57190 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57190
  have eq57345 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57113
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq57113
    | exact resolve eq57113 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57113
  have eq57699 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39206
       have i₂ := eq57285
       grind)
    | exact superpose eq57285 eq39206
    | exact resolve eq39206 eq57285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39206 eq57285
  have eq57808 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57699
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq57699
    | exact resolve eq57699 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57699
  have eq58960 : x = (k (M.op x y) (M.op (M.op x y) y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46510
       have i₂ := eq57290
       grind)
    | exact superpose eq57290 eq46510
    | exact resolve eq46510 eq57290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46510 eq57290
  have eq59085 : x = (k (M.op x y) (M.op (M.op x y) y)) := by
    first
    | (have r₁ := eq58960
       have r₂ := eq2531
       grind)
    | exact resolve eq58960 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2531 eq58960
  have eq59632 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57808 eq2397
    | exact resolve eq2397 eq57808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397 eq57808
  have eq59649 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq59632
    | exact resolve eq59632 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59632
  have eq59691 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59649 eq28
    | exact resolve eq28 eq59649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59649
  have eq59793 : x = (M.op x y) := by
    first
    | (have r₁ := eq59691
       have r₂ := eq57345
       grind)
    | exact resolve eq59691 eq57345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57345 eq59691
  have eq59801 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq59793 eq21
    | exact resolve eq21 eq59793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59948 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq59793 eq47457
    | exact resolve eq47457 eq59793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47457
  have eq59957 : x = (k x (M.op x y)) := by
    first
    | exact superpose eq59793 eq59085
    | exact resolve eq59085 eq59793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59085
  have eq59960 : x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq59957
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59957
    | exact resolve eq59957 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59957
  have eq59964 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq59948
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59948
    | exact resolve eq59948 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq59948
  have eq60070 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq59801
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq59801
    | exact resolve eq59801 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59801
  have eq60071 : x = (k x x) := by
    first
    | exact superpose eq59793 eq59960
    | exact resolve eq59960 eq59793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59960
  have eq60072 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq21 eq59964
    | exact resolve eq59964 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq59964
  have eq60134 : x = (M.op x x) := by
    first
    | (have i₁ := eq60071
       have i₂ := eq39167
       grind)
    | exact superpose eq39167 eq60071
    | exact resolve eq60071 eq39167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39167 eq60071
  have eq60222 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq60070 eq27
    | exact resolve eq27 eq60070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq60573 : (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq60072 eq2916
    | exact resolve eq2916 eq60072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2916
  have eq60615 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq60072 eq515
    | exact resolve eq515 eq60072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515 eq60072
  have eq60645 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq216 eq60615
    | exact resolve eq60615 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq60615
  have eq60677 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq60070 eq60573
    | exact resolve eq60573 eq60070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60573
  have eq60690 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq60070 eq60645
    | exact resolve eq60645 eq60070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60645
  have eq64875 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq52013 eq60690
    | exact resolve eq60690 eq52013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52013 eq60690
  have eq64931 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq60222 eq64875
    | exact resolve eq64875 eq60222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64875
  have eq64944 : y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq64931
       have r₂ := eq28
       grind)
    | exact resolve eq64931 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64931
  have eq64948 : x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq64944
       have i₂ := eq60134
       grind)
    | exact superpose eq60134 eq64944
    | exact resolve eq64944 eq60134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64944
  have eq68697 : y = (M.op (M.op x x) y) ∨ x = y := by
    first
    | (have i₁ := eq3844 y x
       have i₂ := eq64948
       grind)
    | exact superpose eq64948 eq3844
    | exact resolve eq3844 eq64948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3844 eq64948
  have eq68719 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq68697
       have i₂ := eq1102
       grind)
    | exact superpose eq1102 eq68697
    | exact resolve eq68697 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq68697
  have eq68728 : y = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq1499 eq68719
    | exact resolve eq68719 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499 eq68719
  have eq68735 : y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq59793 eq68728
    | exact resolve eq68728 eq59793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59793 eq68728
  have eq68739 : x = y ∨ x = y := by
    first
    | (have i₁ := eq68735
       have i₂ := eq60134
       grind)
    | exact superpose eq60134 eq68735
    | exact resolve eq68735 eq60134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60134 eq68735
  have eq68740 : x = y := by grind
  clear eq68739
  have eq68749 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq68740
       grind)
    | exact superpose eq68740 eq25
    | exact resolve eq25 eq68740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq68740
  have eq68978 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq68749
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq68749
    | exact resolve eq68749 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq68749
  have eq69078 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq60070 eq68978
    | exact resolve eq68978 eq60070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60070 eq68978
  have eq69453 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq69078 eq60222
    | exact resolve eq60222 eq69078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60222 eq69078
  have eq69458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60677 eq69453
    | exact resolve eq69453 eq60677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60677 eq69453
  have eq69564 : False := by grind
  exact eq69564

/-- `Equation2683`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pxx_pxy_Equation2683 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2683 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2683.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X0 x) (M.op x x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq63 X0 (M.op X0 X0)
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq319 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq319 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq322 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq320 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq320 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq320 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq333 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq322 (σ X0)
       grind)
    | exact superpose eq322 eq15
    | exact resolve eq15 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq333 X0
       have i₂ := eq322 X0
       grind)
    | exact superpose eq322 eq333
    | exact resolve eq333 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq333
  have eq400 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq68
    | exact resolve eq68 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq400 X0 X1
       have j1 := eq403 X0 X1
       grind)
    | (have r₁ := eq400 X0 X1
       have r₂ := eq403 X0 X1
       grind)
    | exact resolve eq400 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq403
  have eq747 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq405 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq405
    | exact resolve eq405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq405 X1 (σ X0)
       grind)
    | exact superpose eq405 eq15
    | (have j1 := eq405 X1 (σ X0)
       grind)
    | exact resolve eq15 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq777 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq758 X0 X1
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq758
    | (have j0 := eq758 X0 X1
       grind)
    | exact resolve eq758 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq758
  have eq795 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq747 (τ X1) X0
       grind)
    | exact superpose eq747 eq19
    | (have j1 := eq747 (τ X1) X0
       grind)
    | exact resolve eq19 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq747
  have eq1223 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq795 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq795
    | exact resolve eq795 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq1305 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1223 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1223
    | (have j0 := eq1223 X0 X1
       grind)
    | exact resolve eq1223 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1819 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq777 x y
       grind)
    | exact superpose eq777 eq16
    | (have j1 := eq777 x y
       grind)
    | exact resolve eq16 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq1918 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1819
       have i₂ := eq1305 y x
       grind)
    | exact superpose eq1305 eq1819
    | (have j1 := eq1305 y x
       grind)
    | (have r₁ := eq1819
       have r₂ := eq1305 y x
       grind)
    | exact resolve eq1819 eq1305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305 eq1819
  have eq1919 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1918
  have eq1926 : y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq68 x
       have i₂ := eq1919
       grind)
    | exact superpose eq1919 eq68
    | exact resolve eq68 eq1919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1933 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq404 x
       have i₂ := eq1919
       grind)
    | exact superpose eq1919 eq404
    | exact resolve eq404 eq1919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919
  have eq1980 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1933
       grind)
    | exact superpose eq1933 eq16
    | exact resolve eq16 eq1933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933
  have eq2046 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1980
       have i₂ := eq1926
       grind)
    | exact superpose eq1926 eq1980
    | exact resolve eq1980 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926 eq1980
  have eq2047 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq2046
  have eq2048 : (σ y) = (σ (M.op x x)) := by grind
  clear eq2047
  have eq2055 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq404 x
       have i₂ := eq2048
       grind)
    | exact superpose eq2048 eq404
    | exact resolve eq404 eq2048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq2059 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2048
       grind)
    | exact superpose eq2048 eq10
    | exact resolve eq10 eq2048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048
  have eq2109 : y = (M.op x x) := by
    first
    | (have i₁ := eq2059
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2059
    | exact resolve eq2059 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059
  have eq2115 : y = (M.op x y) := by
    first
    | (have i₁ := eq68 x
       have i₂ := eq2109
       grind)
    | exact superpose eq2109 eq68
    | exact resolve eq68 eq2109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq2109
  have eq2178 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2055
       grind)
    | exact superpose eq2055 eq16
    | exact resolve eq16 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055
  have eq2196 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2178
       have i₂ := eq2115
       grind)
    | exact superpose eq2115 eq2178
    | exact resolve eq2178 eq2115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115 eq2178
  have eq2197 : False := by grind
  exact eq2197

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyy_x_pyx_pxy_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19
    | exact resolve eq19 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq14
    | (have j0 := eq14 X0 X1
       grind)
    | exact resolve eq14 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X1 : G, (k X1 X1) = (M.op (k X1 X1) (k X1 X1)) ∨ (M.op (M.op X1 X1) X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq140 : ∀ X1 : G, (k X1 X1) = (k (k X1 X1) (k X1 X1)) ∨ (M.op (M.op X1 X1) X1) = (k (M.op X1 X1) X1) := by
    intro X1
    first
    | (have i₁ := eq139 X1
       have i₂ := eq136 (k X1 X1)
       grind)
    | exact superpose eq136 eq139
    | (have j0 := eq139 X1
       grind)
    | exact resolve eq139 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq141 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq138 X0 X1
       have i₂ := eq136 X1
       grind)
    | exact superpose eq136 eq138
    | (have j0 := eq138 X0 X1
       grind)
    | exact resolve eq138 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq142 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 X1
       have i₂ := eq136 X1
       grind)
    | exact superpose eq136 eq137
    | (have j0 := eq137 X0 X1
       grind)
    | (have r₁ := eq137 X0 X0
       have r₂ := eq136 X0
       grind)
    | exact resolve eq137 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq143 : ∀ X1 : G, (M.op (k X1 X1) X1) = (k (k X1 X1) X1) ∨ (k X1 X1) = (k (k X1 X1) (k X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq140 x
       have i₂ := eq136 x
       grind)
    | exact superpose eq136 eq140
    | (have j0 := eq140 X1
       grind)
    | exact resolve eq140 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq144 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k X0 X0) = (k X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 X1
       have i₂ := eq136 X1
       grind)
    | exact superpose eq136 eq141
    | (have j0 := eq141 X0 X1
       grind)
    | exact resolve eq141 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq145 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq144 X0 X1
       have j1 := eq142 X0 X1
       grind)
    | (have r₁ := eq144 (k X1 X1) X0
       have r₂ := eq142 X0 X1
       grind)
    | (have r₁ := eq144 (k X0 X0) X1
       have r₂ := eq142 X0 X1
       grind)
    | (have r₁ := eq144 X0 X1
       have r₂ := eq142 X0 X1
       grind)
    | exact resolve eq144 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq146 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (k X0 X0)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 X0
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq9
    | exact resolve eq9 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq136 (M.op X0 X1)
       grind)
    | exact superpose eq136 eq9
    | exact resolve eq9 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (k X2 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq146 X2 (M.op (M.op X0 X1) (M.op X2 X1))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq146
    | exact resolve eq146 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 : G, (M.op (M.op (k X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq146 X0 X0
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq146
    | exact resolve eq146 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (k X1 X1)) = (M.op (M.op X0 (M.op X2 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (k X1 X1)) X1 X2
       have i₂ := eq146 X1 X0
       grind)
    | exact superpose eq146 eq9
    | exact resolve eq9 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq155 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq154 (M.op X0 X1) X1 x
       grind)
    | exact superpose eq154 eq9
    | exact resolve eq9 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : ∀ X0 : G, (M.op (k (k X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq151 X0
       have i₂ := eq136 (k X0 X0)
       grind)
    | exact superpose eq136 eq151
    | exact resolve eq151 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq160 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (k X1 X1)) (k (k X1 X1) (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq155 (M.op (M.op X0 X1) X1) (k X1 X1)
       have i₂ := eq155 X0 X1
       grind)
    | exact superpose eq155 eq155
    | exact resolve eq155 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq155 (k (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq148 X0 X1
       grind)
    | exact superpose eq148 eq155
    | exact resolve eq155 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq166 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq165 X0 X1
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq165
    | exact resolve eq165 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq167 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq166 X0 X1
       have i₂ := eq136 (k X0 X0)
       grind)
    | exact superpose eq136 eq166
    | exact resolve eq166 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq174 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq145 (σ y) (σ x)
       grind)
    | exact superpose eq145 eq16
    | (have j1 := eq145 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (M.op X1 X0)) = (M.op (M.op X0 (M.op X2 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37 X0 X0 X1 X2
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq37
    | exact resolve eq37 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 X2 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) X0) = (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37 (M.op X0 X1) X2 X1 X0
       have i₂ := eq136 (M.op X0 X1)
       grind)
    | exact superpose eq136 eq37
    | exact resolve eq37 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X2 X3)) (k (M.op X2 X3) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq155 (M.op X0 X3) (M.op X2 X3)
       have i₂ := eq37 X0 X3 X2 X1
       grind)
    | exact superpose eq37 eq155
    | exact resolve eq155 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (k X3 (M.op X0 (M.op X3 X2))) ∨ (k (M.op X0 (M.op X3 X2)) (M.op X0 (M.op X3 X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq145 X3 (M.op X0 (M.op X3 X2))
       have i₂ := eq37 X0 X1 X2 X3
       grind)
    | exact superpose eq37 eq145
    | (have j0 := eq145 X3 (M.op X0 (M.op X3 X2))
       grind)
    | exact resolve eq145 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 X1 X2 X3 : G, (k (k X0 X0) (k X0 X0)) = X3 ∨ (M.op (M.op X0 X1) (M.op X2 X1)) = (k X3 (M.op X0 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq406 X0 X1 X2 X3
       have i₂ := eq167 X0 (M.op X3 X2)
       grind)
    | exact superpose eq167 eq406
    | (have j0 := eq406 X0 X1 X2 X3
       grind)
    | exact resolve eq406 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq410 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X2 X3)) (k (k X2 X2) (k X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq405 X0 X1 X2 X3
       have i₂ := eq167 X2 X3
       grind)
    | exact superpose eq167 eq405
    | exact resolve eq405 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq417 : ∀ X0 X1 X2 : G, (M.op (k (k X0 X0) (k X0 X0)) X0) = (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq395 X0 X1 X2
       have i₂ := eq167 X0 X1
       grind)
    | exact superpose eq167 eq395
    | exact resolve eq395 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq433 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 X0)) = (M.op (M.op X0 X1) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq154 X0 X1 x
       have i₂ := eq370 X0 X1 x
       grind)
    | exact superpose eq370 eq154
    | exact resolve eq154 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq434 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op (k X0 X0) (M.op X2 X0)) (M.op X2 X3)) (k (k X2 X2) (k X2 X2))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq410 X0 x X2 X3
       have i₂ := eq370 X0 X2 x
       grind)
    | exact superpose eq370 eq410
    | exact resolve eq410 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq439 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq417 X0 X1 X2
       have i₂ := eq157 X0
       grind)
    | exact superpose eq157 eq417
    | exact resolve eq417 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq451 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (k X0 X0) (M.op (k X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq160 X0 X1
       have i₂ := eq433 X0 (k X1 X1)
       grind)
    | exact superpose eq433 eq160
    | exact resolve eq160 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq452 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) (M.op X1 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq155 X0 X1
       have i₂ := eq433 (M.op X0 X1) X1
       grind)
    | exact superpose eq433 eq155
    | exact resolve eq155 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq433
  have eq475 : ∀ X0 X1 : G, (M.op (k (k X0 X0) (k X0 X0)) (M.op X1 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq452 X0 X1
       have i₂ := eq167 X0 X1
       grind)
    | exact superpose eq167 eq452
    | exact resolve eq452 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq507 : ∀ X0 X1 : G, (M.op (k (k X1 X1) (k X1 X1)) (M.op X0 (k X0 X1))) = X1 ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq475 X1 X0
       have i₂ := eq145 X0 X1
       grind)
    | exact superpose eq145 eq475
    | (have j1 := eq145 X0 X1
       grind)
    | exact resolve eq475 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (k (k (M.op X0 X3) (M.op X0 X3)) (k (M.op X0 X3) (M.op X0 X3))) (M.op (M.op X2 X3) (M.op (M.op X0 (M.op X1 X2)) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq475 (M.op X0 X3) (M.op X2 X3)
       have i₂ := eq37 X0 X3 X2 X1
       grind)
    | exact superpose eq37 eq475
    | exact resolve eq475 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) = (M.op (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (M.op (M.op X1 (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq475 (k (k X0 X0) (k X0 X0)) (M.op X1 (M.op X0 X1))
       have i₂ := eq475 X0 X1
       grind)
    | exact superpose eq475 eq475
    | exact resolve eq475 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X3 (k (k X0 X0) (k X0 X0)))) X3) = (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37 X1 (M.op X2 (M.op X0 X2)) (k (k X0 X0) (k X0 X0)) X3
       have i₂ := eq475 X0 X2
       grind)
    | exact superpose eq475 eq37
    | exact resolve eq37 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq522 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X0) = (M.op (k X1 X1) (M.op (k (k X0 X0) (k X0 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq518 X0 X1 X2 x
       have i₂ := eq370 X1 (k (k X0 X0) (k X0 X0)) x
       grind)
    | exact superpose eq370 eq518
    | exact resolve eq518 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq523 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) = (M.op (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (M.op (k X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq513 X0 X1
       have i₂ := eq370 X1 X1 X0
       grind)
    | exact superpose eq370 eq513
    | exact resolve eq513 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq526 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (k (k (M.op X0 X3) (M.op X0 X3)) (k (M.op X0 X3) (M.op X0 X3))) (M.op (M.op X2 X3) (M.op (k X0 X0) (M.op X2 X0)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq509 X0 x X2 X3
       have i₂ := eq370 X0 X2 x
       grind)
    | exact superpose eq370 eq509
    | exact resolve eq509 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq530 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) = (M.op (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (M.op (k X1 X1) (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X0 X1
       have i₂ := eq136 X1
       grind)
    | exact superpose eq136 eq523
    | exact resolve eq523 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq532 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (M.op (M.op X2 X3) (M.op (k X0 X0) (M.op X2 X0)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq526 X0 X2 x
       have i₂ := eq167 X0 x
       grind)
    | exact superpose eq167 eq526
    | exact resolve eq526 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq533 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) = (M.op (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (k (k X1 X1) (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq530 X0 X1
       have i₂ := eq136 (k X1 X1)
       grind)
    | exact superpose eq136 eq530
    | exact resolve eq530 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq536 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq439 X0 X0 X1
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq439
    | exact resolve eq439 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq439 (M.op (M.op X0 X1) X2) (M.op X1 X2) X3
       have i₂ := eq439 X0 X1 X2
       grind)
    | exact superpose eq439 eq439
    | exact resolve eq439 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq439 (M.op X0 X1) X2 (M.op X1 X2)
       have i₂ := eq439 X0 X1 X2
       grind)
    | exact superpose eq439 eq439
    | exact resolve eq439 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (k X1 X1) (M.op (k (k X0 X0) (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq522 X0 X1 x
       have i₂ := eq547 X1 X0 x
       grind)
    | exact superpose eq547 eq522
    | exact resolve eq522 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq601 : ∀ X0 X1 : G, (M.op (k X1 X1) (M.op (k X0 X0) X1)) = (M.op (k X1 X1) (M.op (k (k X0 X0) (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq581 X0 X1
       have i₂ := eq451 X1 X0
       grind)
    | exact superpose eq451 eq581
    | exact resolve eq581 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq649 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X2)) = (M.op (M.op (k (M.op X0 (M.op X3 X2)) (M.op X0 (M.op X3 X2))) X3) (M.op (M.op X0 X1) (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq536 (M.op X0 (M.op X3 X2)) X3
       have i₂ := eq37 X0 X1 X2 X3
       grind)
    | exact superpose eq37 eq536
    | exact resolve eq536 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (k X0 X0) X1) (M.op X3 X2)) X3) = (M.op X0 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37 (M.op (k X0 X0) X1) (M.op X0 X1) X2 X3
       have i₂ := eq536 X0 X1
       grind)
    | exact superpose eq536 eq37
    | exact resolve eq37 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq668 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 X1))) = (M.op (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) (M.op X2 (M.op (k X0 X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq661 X0 X1 X2 x
       have i₂ := eq370 (M.op (k X0 X0) X1) X2 x
       grind)
    | exact superpose eq370 eq661
    | exact resolve eq661 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq680 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X2)) = (M.op (M.op (k (k X0 X0) (k X0 X0)) X3) (M.op (M.op X0 X1) (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq649 X0 X1 X2 X3
       have i₂ := eq167 X0 (M.op X3 X2)
       grind)
    | exact superpose eq167 eq649
    | exact resolve eq649 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq684 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 X1))) = (M.op (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (M.op X2 (M.op (k X0 X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq668 X0 X1 X2
       have i₂ := eq167 (k X0 X0) X1
       grind)
    | exact superpose eq167 eq668
    | exact resolve eq668 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq692 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X2 X3) (M.op X0 (M.op X2 X0)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq532 X0 X2 X3
       have i₂ := eq684 X0 (M.op X2 X0) (M.op X2 X3)
       grind)
    | exact superpose eq684 eq532
    | exact resolve eq532 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq684
  have eq697 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X2 X3) X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq692 X0 X2 X3
       have i₂ := eq547 (M.op X2 X3) X2 X0
       grind)
    | exact superpose eq547 eq692
    | exact resolve eq692 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq707 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (k X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq697 X1 X0 X0
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq697
    | exact resolve eq697 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (k (k X0 X0) X0) (k X0 X0))) ∨ (k X0 X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq697 X1 (k X0 X0) X0
       have i₂ := eq143 X0
       grind)
    | exact superpose eq143 eq697
    | (have j1 := eq143 X0
       grind)
    | exact resolve eq697 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq717 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) (M.op X2 X1))) = (M.op X3 (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq697 X3 X0 (M.op X0 X2)
       have i₂ := eq37 X0 X1 X2 X0
       grind)
    | exact superpose eq37 eq697
    | exact resolve eq697 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op X3 (M.op (M.op (M.op X0 X1) (M.op X2 X0)) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq697 X3 (M.op X0 X1) X1
       have i₂ := eq37 (M.op X0 X1) X1 X0 X2
       grind)
    | exact superpose eq37 eq697
    | exact resolve eq697 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (k (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq157 (M.op (M.op X0 X1) X0)
       have i₂ := eq697 (k (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0))) X0 X1
       grind)
    | exact superpose eq697 eq157
    | exact resolve eq157 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq745 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (k (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq742 X1 X1
       have i₂ := eq167 (M.op X1 X1) X1
       grind)
    | exact superpose eq167 eq742
    | exact resolve eq742 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq761 : ∀ X0 X1 X3 : G, (M.op X3 X1) = (M.op X3 (M.op (k (M.op X0 X1) (M.op X0 X1)) (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq718 X0 X1 x X3
       have i₂ := eq370 (M.op X0 X1) X0 x
       grind)
    | exact superpose eq370 eq718
    | exact resolve eq718 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq763 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 X1 X2 x
       have i₂ := eq717 X0 x X2 (M.op (M.op X1 X2) X0)
       grind)
    | exact superpose eq717 eq38
    | exact resolve eq38 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq765 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X2)) = (M.op (M.op (k (k X0 X0) (k X0 X0)) X3) (M.op X0 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq680 X0 x X2 X3
       have i₂ := eq717 X0 x X2 (M.op (k (k X0 X0) (k X0 X0)) X3)
       grind)
    | exact superpose eq717 eq680
    | exact resolve eq680 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq774 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq745 X0 X1
       have i₂ := eq167 X0 X1
       grind)
    | exact superpose eq167 eq745
    | exact resolve eq745 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq784 : ∀ X0 X1 X3 : G, (M.op X3 X1) = (M.op X3 (M.op (k (k X0 X0) (k X0 X0)) (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq761 X0 X1 X3
       have i₂ := eq167 X0 X1
       grind)
    | exact superpose eq167 eq761
    | exact resolve eq761 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq814 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq763 X1 X0 X0
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq763
    | exact resolve eq763 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq439 (M.op X0 X1) X2 (M.op X2 X1)
       have i₂ := eq763 X2 X0 X1
       grind)
    | exact superpose eq763 eq439
    | exact resolve eq439 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq845 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X4 (M.op (M.op X0 X3) X2))) X4) = (M.op (M.op X1 (M.op X2 X3)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq37 X1 (M.op X2 X3) (M.op (M.op X0 X3) X2) X4
       have i₂ := eq763 X2 X0 X3
       grind)
    | exact superpose eq763 eq37
    | exact resolve eq37 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq850 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (k (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq536 (M.op (M.op X0 X1) X2) (M.op X2 X1)
       have i₂ := eq763 X2 X0 X1
       grind)
    | exact superpose eq763 eq536
    | exact resolve eq536 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq851 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq850 X0 X1 X2
       have i₂ := eq167 (M.op X0 X1) X2
       grind)
    | exact superpose eq167 eq850
    | exact resolve eq850 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq853 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) X0) = (M.op (k X1 X1) (M.op (M.op (M.op X0 X3) X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq845 X0 X1 X2 X3 x
       have i₂ := eq370 X1 (M.op (M.op X0 X3) X2) x
       grind)
    | exact superpose eq370 eq845
    | exact resolve eq845 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq855 : ∀ X0 X1 X3 : G, (M.op X3 X1) = (M.op X3 (M.op (k (k X0 X0) (k X0 X0)) X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq784 X0 X1 X3
       have i₂ := eq842 (k (k X0 X0) (k X0 X0)) X1 X0
       grind)
    | exact superpose eq842 eq784
    | exact resolve eq784 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq872 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq851 X0 X1 X2
       have i₂ := eq167 X0 X1
       grind)
    | exact superpose eq167 eq851
    | exact resolve eq851 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq877 : ∀ X0 X1 : G, (M.op (k X1 X1) X1) = (M.op (k X1 X1) (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq601 X0 X1
       have i₂ := eq855 X0 X1 (k X1 X1)
       grind)
    | exact superpose eq855 eq601
    | exact resolve eq601 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq895 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 X1
       have i₂ := eq877 X1 X0
       grind)
    | exact superpose eq877 eq451
    | exact resolve eq451 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq877
  have eq914 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X2 X3)) = (M.op (k (M.op X0 X3) (M.op X0 X3)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq895 (M.op X0 X3) (M.op X2 X3)
       have i₂ := eq37 X0 X3 X2 X1
       grind)
    | exact superpose eq37 eq895
    | exact resolve eq895 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (k (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq895 (M.op (M.op X0 X1) X2) (M.op X1 X2)
       have i₂ := eq439 X0 X1 X2
       grind)
    | exact superpose eq439 eq895
    | exact resolve eq895 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq916 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X1)) = (M.op (k (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq895 (M.op (M.op X0 X1) X2) (M.op X2 X1)
       have i₂ := eq763 X2 X0 X1
       grind)
    | exact superpose eq763 eq895
    | exact resolve eq895 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq917 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq895 (M.op (k X0 X0) X1) (M.op X0 X1)
       have i₂ := eq536 X0 X1
       grind)
    | exact superpose eq536 eq895
    | exact resolve eq895 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq944 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq917 X0 X1
       have i₂ := eq167 (k X0 X0) X1
       grind)
    | exact superpose eq167 eq917
    | exact resolve eq917 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq945 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X1)) = (M.op (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq916 X0 X1 X2
       have i₂ := eq167 (M.op X0 X1) X2
       grind)
    | exact superpose eq167 eq916
    | exact resolve eq916 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq946 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq915 X0 X1 X2
       have i₂ := eq167 (M.op X0 X1) X2
       grind)
    | exact superpose eq167 eq915
    | exact resolve eq915 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq947 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X2 X3)) = (M.op (k (k X0 X0) (k X0 X0)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq914 X0 X1 X2 X3
       have i₂ := eq167 X0 X3
       grind)
    | exact superpose eq167 eq914
    | exact resolve eq914 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq955 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X1)) = (M.op (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq945 X0 X1 X2
       have i₂ := eq167 X0 X1
       grind)
    | exact superpose eq167 eq945
    | exact resolve eq945 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq956 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq946 X0 X1 X2
       have i₂ := eq167 X0 X1
       grind)
    | exact superpose eq167 eq946
    | exact resolve eq946 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq957 : ∀ X0 X2 X3 : G, (M.op (M.op (k X0 X0) (M.op X2 X0)) (M.op X2 X3)) = (M.op (k (k X0 X0) (k X0 X0)) (M.op X0 X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq947 X0 x X2 X3
       have i₂ := eq370 X0 X2 x
       grind)
    | exact superpose eq370 eq947
    | exact resolve eq947 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq947
  have eq969 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (k (k X0 X0) (k X0 X0)) (M.op X0 X3)) (k (k X2 X2) (k X2 X2))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq434 X0 X2 X3
       have i₂ := eq957 X0 X2 X3
       grind)
    | exact superpose eq957 eq434
    | exact resolve eq434 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434 eq957
  have eq976 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) (k X0 X1)) = X0 ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq814 X0 X1
       have i₂ := eq145 X0 X1
       grind)
    | exact superpose eq145 eq814
    | (have j1 := eq145 X0 X1
       grind)
    | exact resolve eq814 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq997 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (M.op (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq536 (M.op (k X0 X0) X1) (M.op X1 X0)
       have i₂ := eq814 X0 X1
       grind)
    | exact superpose eq814 eq536
    | exact resolve eq536 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq1002 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (k (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1))) (M.op (M.op (M.op X0 X0) X1) (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq997 X0 X1
       have i₂ := eq853 X0 (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) X1 X0
       grind)
    | exact superpose eq853 eq997
    | exact resolve eq997 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853 eq997
  have eq1023 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (M.op (M.op (M.op X0 X0) X1) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1002 X0 X1
       have i₂ := eq167 (k X0 X0) X1
       grind)
    | exact superpose eq167 eq1002
    | exact resolve eq1002 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1031 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (k (k (k (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))))) (k (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))))) (k (k (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))))) (k (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))))))) (M.op (M.op (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1023 X0 X1
       have i₂ := eq955 (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq955 eq1023
    | exact resolve eq1023 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq1023
  have eq1034 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (M.op (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1031 X0 X1
       have i₂ := eq956 (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq956 eq1031
    | exact resolve eq1031 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956 eq1031
  have eq1037 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1034 X0 X1
       have i₂ := eq855 (k X0 X0) (M.op (M.op X0 X0) X1) (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))))
       grind)
    | exact superpose eq855 eq1034
    | exact resolve eq1034 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq1034
  have eq1039 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1037 X0 X1
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq1037
    | exact resolve eq1037 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1040 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq547 X1 X0 X0
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq547
    | exact resolve eq547 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1043 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq547 X3 (M.op X0 (M.op X4 X2)) X4
       have i₂ := eq37 X0 X1 X2 X4
       grind)
    | exact superpose eq37 eq547
    | exact resolve eq547 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq1044 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (k X0 X0) X0))) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq547 X1 (M.op X0 X2) X2
       have i₂ := eq895 X0 X2
       grind)
    | exact superpose eq895 eq547
    | exact resolve eq547 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1049 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (k X0 X0) X2)) = (M.op X1 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq547 X1 (M.op (k X0 X0) X2) (M.op X2 X0)
       have i₂ := eq814 X0 X2
       grind)
    | exact superpose eq814 eq547
    | exact resolve eq547 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq1051 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq547 X1 (k (k X0 X0) (k X0 X0)) X0
       have i₂ := eq157 X0
       grind)
    | exact superpose eq157 eq547
    | exact resolve eq547 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1089 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (k (k (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) (k (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq157 (M.op X0 (M.op X1 X0))
       have i₂ := eq547 (k (k (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) (k (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) X1 X0
       grind)
    | exact superpose eq547 eq157
    | exact resolve eq157 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1093 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1089 X0 X1
       have i₂ := eq167 X0 (M.op X1 X0)
       grind)
    | exact superpose eq167 eq1089
    | exact resolve eq1089 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1121 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = (M.op X1 (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1051 X0 X1
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq1051
    | exact resolve eq1051 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq1123 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (k X0 X0) X2)) = (M.op X1 (M.op (k X2 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1049 X0 X1 X2
       have i₂ := eq895 X2 X0
       grind)
    | exact superpose eq895 eq1049
    | exact resolve eq1049 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895 eq1049
  have eq1127 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1044 X0 X1 X2
       have i₂ := eq707 X0 X2
       grind)
    | exact superpose eq707 eq1044
    | exact resolve eq1044 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1128 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op X0 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1043 X0 x X2 X3 X4
       have i₂ := eq717 X0 x X2 X4
       grind)
    | exact superpose eq717 eq1043
    | exact resolve eq1043 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717 eq1043
  have eq1153 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (k (k X0 X0) (k X0 X0)) (M.op X0 X3)) (k X2 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq969 X0 X2 X3
       have i₂ := eq1121 X2 (M.op (k (k X0 X0) (k X0 X0)) (M.op X0 X3))
       grind)
    | exact superpose eq1121 eq969
    | exact resolve eq969 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq1155 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) = (M.op (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq533 X0 X1
       have i₂ := eq1121 X1 (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))))
       grind)
    | exact superpose eq1121 eq533
    | exact resolve eq533 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq1121
  have eq1157 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (k X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1123 X0 X1 X2
       have i₂ := eq707 X2 X1
       grind)
    | exact superpose eq707 eq1123
    | exact resolve eq1123 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq1123
  have eq1162 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (k X0 X0) (k (k X0 X0) X0))) ∨ (k X0 X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 X1
       have i₂ := eq1127 (k X0 X0) X1 (k (k X0 X0) X0)
       grind)
    | (have i₁ := eq716 X0 X1
       have i₂ := eq1127 (k (k X0 X0) X0) X1 (k X0 X0)
       grind)
    | exact superpose eq1127 eq716
    | (have j0 := eq716 X0 X1
       grind)
    | exact resolve eq716 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq1202 : ∀ X0 X1 : G, (M.op (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq944 X0 X1
       have i₂ := eq1157 X0 (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) X1
       grind)
    | exact superpose eq1157 eq944
    | exact resolve eq944 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq1203 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1039 X0 X1
       have i₂ := eq1157 X0 (k (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) X1
       grind)
    | exact superpose eq1157 eq1039
    | exact resolve eq1039 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1206 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (M.op X1 X0) = (M.op X1 (k (k X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1162 X0 X1
       have i₂ := eq1157 X0 X1 (k (k X0 X0) X0)
       grind)
    | exact superpose eq1157 eq1162
    | (have j0 := eq1162 X0 X1
       grind)
    | exact resolve eq1162 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1220 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq774 X0 X1
       have i₂ := eq1203 X0 X1
       grind)
    | exact superpose eq1203 eq774
    | exact resolve eq774 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq1237 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) = (M.op (k X0 X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1155 X0 X1
       have i₂ := eq1203 X0 (k X1 X1)
       grind)
    | exact superpose eq1203 eq1155
    | exact resolve eq1155 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155 eq1203
  have eq1243 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op X0 (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq872 X0 X1 X2
       have i₂ := eq1202 X0 (M.op X2 X1)
       grind)
    | exact superpose eq1202 eq872
    | exact resolve eq872 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq1266 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (k X0 X0) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1243 X0 X1 X2
       have i₂ := eq1220 X0 (M.op X0 (M.op X2 X1))
       grind)
    | exact superpose eq1220 eq1243
    | exact resolve eq1243 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq1243
  have eq1296 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (k X0 X0) (M.op X0 (M.op X2 (k X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq149 X0 X1 X2
       have i₂ := eq1266 X0 (k X2 X2) X2
       grind)
    | exact superpose eq1266 eq149
    | exact resolve eq149 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq1321 : ∀ X0 X1 : G, (M.op (k (k X0 X0) (k X0 X0)) (M.op (k X0 X0) (M.op (k X0 X1) X1))) = X0 ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq976 X0 X1
       have i₂ := eq1266 (k X0 X0) X1 (k X0 X1)
       grind)
    | exact superpose eq1266 eq976
    | (have j0 := eq976 X0 X1
       grind)
    | exact resolve eq976 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq1329 : ∀ X0 X1 : G, (M.op (k (k X0 X0) (k X0 X0)) (M.op (k X0 X1) X1)) = X0 ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1321 X0 X1
       have i₂ := eq1157 X0 (k (k X0 X0) (k X0 X0)) (M.op (k X0 X1) X1)
       grind)
    | exact superpose eq1157 eq1321
    | (have j0 := eq1321 X0 X1
       grind)
    | exact resolve eq1321 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1353 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (k X0 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1296 X0 X1 X2
       have i₂ := eq1040 X2 X0
       grind)
    | exact superpose eq1040 eq1296
    | exact resolve eq1296 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040 eq1296
  have eq1371 : ∀ X0 X1 : G, (M.op (k (k X0 X0) (k X0 X0)) (M.op X1 (k X0 X1))) = X0 ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1329 X0 X1
       have i₂ := eq1127 X1 (k (k X0 X0) (k X0 X0)) (k X0 X1)
       grind)
    | (have i₁ := eq1329 X0 X1
       have i₂ := eq1127 (k X0 X1) (k (k X0 X0) (k X0 X0)) X1
       grind)
    | exact superpose eq1127 eq1329
    | (have j0 := eq1329 X0 X1
       grind)
    | exact resolve eq1329 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329
  have eq1395 : ∀ X0 X2 X3 : G, (k X3 (M.op X0 (M.op X3 X2))) = (M.op (k X0 X0) (M.op X0 X2)) ∨ (k (k X0 X0) (k X0 X0)) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq409 X0 x X2 X3
       have i₂ := eq1353 X0 x X2
       grind)
    | exact superpose eq1353 eq409
    | (have j0 := eq409 X0 x X2 X3
       grind)
    | exact resolve eq409 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq1408 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (k X0 X0) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq540 X0 X1 X2 x
       have i₂ := eq1353 X0 x (M.op X1 X2)
       grind)
    | exact superpose eq1353 eq540
    | exact resolve eq540 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq1353
  have eq1491 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X2)) = (M.op (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (M.op (k (k X0 X0) (k X0 X0)) (M.op X3 (M.op X0 X2)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq765 X0 X2 X3
       have i₂ := eq1408 (k (k X0 X0) (k X0 X0)) X3 (M.op X0 X2)
       grind)
    | exact superpose eq1408 eq765
    | exact resolve eq765 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq1498 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (M.op (k (k X0 X0) (k X0 X0)) (M.op (M.op X0 X3) (k X2 X2)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1153 X0 X2 X3
       have i₂ := eq1408 (k (k X0 X0) (k X0 X0)) (M.op X0 X3) (k X2 X2)
       grind)
    | exact superpose eq1408 eq1153
    | exact resolve eq1153 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq1531 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (M.op (M.op X0 X3) (k X2 X2))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1498 X0 X2 X3
       have i₂ := eq1157 (k X0 X0) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (M.op (M.op X0 X3) (k X2 X2))
       grind)
    | exact superpose eq1157 eq1498
    | exact resolve eq1498 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq1538 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X2)) = (M.op (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (M.op X3 (M.op X0 X2))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1491 X0 X2 X3
       have i₂ := eq1157 (k X0 X0) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) (M.op X3 (M.op X0 X2))
       grind)
    | exact superpose eq1157 eq1491
    | exact resolve eq1491 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491
  have eq1596 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 (M.op (M.op X0 X3) (k X2 X2)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1531 X0 X2 X3
       have i₂ := eq1202 X0 (M.op (M.op X0 X3) (k X2 X2))
       grind)
    | exact superpose eq1202 eq1531
    | exact resolve eq1531 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1531
  have eq1603 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X2)) = (M.op X0 (M.op X0 (M.op X3 (M.op X0 X2)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1538 X0 X2 X3
       have i₂ := eq1202 X0 (M.op X3 (M.op X0 X2))
       grind)
    | exact superpose eq1202 eq1538
    | exact resolve eq1538 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202 eq1538
  have eq1653 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 (M.op (k X0 X0) (M.op X0 (M.op X3 (k X2 X2)))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1596 X0 X2 X3
       have i₂ := eq1408 X0 X3 (k X2 X2)
       grind)
    | exact superpose eq1408 eq1596
    | exact resolve eq1596 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq1691 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op X0 (M.op (k X0 X0) (M.op X3 (k X2 X2)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1653 X0 X2 X3
       have i₂ := eq1603 X0 (M.op X3 (k X2 X2)) (k X0 X0)
       grind)
    | exact superpose eq1603 eq1653
    | exact resolve eq1653 eq1603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603 eq1653
  have eq1723 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X3 (k X2 X2))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1691 X0 X2 X3
       have i₂ := eq1157 X0 X0 (M.op X3 (k X2 X2))
       grind)
    | exact superpose eq1157 eq1691
    | exact resolve eq1691 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691
  have eq1882 : ∀ X0 X1 X2 : G, (M.op X1 (k X2 X2)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq842 X1 (k X2 X2) X0
       have i₂ := eq1723 X0 X2 X0
       grind)
    | exact superpose eq1723 eq842
    | exact resolve eq842 eq1723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1902 : ∀ X0 X1 X2 : G, (M.op X1 (k X0 X0)) = (M.op X1 (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1882 X2 X1 X0
       have i₂ := eq136 X2
       grind)
    | exact superpose eq136 eq1882
    | exact resolve eq1882 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1882
  have eq2194 : ∀ X0 X1 X2 : G, (M.op X1 (k X2 X2)) = (M.op X1 (τ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1902 X2 X1 (τ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq1902
    | exact resolve eq1902 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2252 : (k (σ y) (σ x)) ≠ (σ (k y x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq174
       have i₂ := eq145 y x
       grind)
    | exact superpose eq145 eq174
    | (have j1 := eq145 (σ y) (σ x)
       grind)
    | exact resolve eq174 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq2253 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have r₁ := eq2252
       have r₂ := eq15 y x
       grind)
    | exact resolve eq2252 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2252
  have eq2637 : y = (τ (k (σ x) (σ x))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2253
       grind)
    | exact superpose eq2253 eq10
    | exact resolve eq10 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2253
  have eq2638 : y = (k x (τ (σ x))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq2637
       have i₂ := eq21 (σ x) x
       grind)
    | exact superpose eq21 eq2637
    | exact resolve eq2637 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2637
  have eq2641 : y = (k x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq2638
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2638
    | exact resolve eq2638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638
  have eq2642 : y = (k x x) := by grind
  clear eq2641
  have eq2644 : ∀ X0 : G, y ≠ (k X0 X0) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq142 x X0
       have i₂ := eq2642
       grind)
    | exact superpose eq2642 eq142
    | (have j0 := eq142 x X0
       grind)
    | exact resolve eq142 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2645 : ∀ X0 : G, y ≠ (k X0 X0) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq142 X0 x
       have i₂ := eq2642
       grind)
    | exact superpose eq2642 eq142
    | (have j0 := eq142 X0 x
       grind)
    | exact resolve eq142 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq2647 : x = (M.op (k y y) x) := by
    first
    | (have i₁ := eq157 x
       have i₂ := eq2642
       grind)
    | exact superpose eq2642 eq157
    | exact resolve eq157 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2650 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1157 x X0 X1
       have i₂ := eq2642
       grind)
    | exact superpose eq2642 eq1157
    | exact resolve eq1157 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2652 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (M.op (k X0 X0) y) := by
    intro X0
    first
    | (have i₁ := eq1237 X0 x
       have i₂ := eq2642
       grind)
    | exact superpose eq2642 eq1237
    | exact resolve eq1237 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq2653 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1723 X0 x X1
       have i₂ := eq2642
       grind)
    | exact superpose eq2642 eq1723
    | exact resolve eq1723 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723
  have eq2658 : ∀ X0 X1 : G, (M.op X0 (k X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1902 X1 X0 x
       have i₂ := eq2642
       grind)
    | exact superpose eq2642 eq1902
    | exact resolve eq1902 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902
  have eq2662 : ∀ X0 X1 : G, (M.op X0 (k X1 X1)) = (M.op X0 (τ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2194 x X0 X1
       have i₂ := eq2642
       grind)
    | exact superpose eq2642 eq2194
    | exact resolve eq2194 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194
  have eq2664 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq15 x x
       have i₂ := eq2642
       grind)
    | exact superpose eq2642 eq15
    | exact resolve eq15 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2665 : (σ (M.op x y)) ≠ (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2664
       grind)
    | exact superpose eq2664 eq16
    | exact resolve eq16 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2717 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq2662 X0 x
       have i₂ := eq2658 X0 x
       grind)
    | exact superpose eq2658 eq2662
    | exact resolve eq2662 eq2658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662
  have eq2719 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq2665
       have i₂ := eq2658 (σ x) (σ x)
       grind)
    | exact superpose eq2658 eq2665
    | exact resolve eq2665 eq2658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2665
  have eq2784 : (σ (M.op x y)) ≠ (k y (σ x)) ∨ y = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2719
       have i₂ := eq145 y (σ x)
       grind)
    | exact superpose eq145 eq2719
    | (have j1 := eq145 y (σ x)
       grind)
    | exact resolve eq2719 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2790 : (k (τ y) (τ y)) = (M.op (τ y) y) := by
    first
    | (have i₁ := eq136 (τ y)
       have i₂ := eq2717 (τ y)
       grind)
    | exact superpose eq2717 eq136
    | exact resolve eq136 eq2717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2791 : ∀ X0 : G, (M.op X0 y) = (k (τ y) X0) ∨ (k X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq145 (τ y) X0
       have i₂ := eq2717 X0
       grind)
    | exact superpose eq2717 eq145
    | (have j0 := eq145 (τ y) X0
       grind)
    | exact resolve eq145 eq2717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717
  have eq2810 : (τ (k y y)) = (M.op (τ y) y) := by
    first
    | (have i₁ := eq2790
       have i₂ := eq29 y y
       grind)
    | exact superpose eq29 eq2790
    | exact resolve eq2790 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2790
  have eq2836 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k y X0)) ∨ y = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2653 X1 X0
       have i₂ := eq145 y X0
       grind)
    | exact superpose eq145 eq2653
    | (have j1 := eq145 y X0
       grind)
    | exact resolve eq2653 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq3558 : ∀ X0 : G, x = (M.op (k y y) (M.op X0 (k X0 x))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq507 X0 x
       have i₂ := eq2642
       grind)
    | exact superpose eq2642 eq507
    | exact resolve eq507 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq4094 : y = (k (k (k y y) (k y y)) (k (k y y) (k y y))) := by
    first
    | (have i₁ := eq157 y
       have i₂ := eq2652 (k y y)
       grind)
    | exact superpose eq2652 eq157
    | exact resolve eq157 eq2652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5101 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op X1 (k X1 x))) ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1157 y X0 (M.op X1 (k X1 x))
       have i₂ := eq3558 X1
       grind)
    | exact superpose eq3558 eq1157
    | (have j1 := eq3558 X1
       grind)
    | exact resolve eq1157 eq3558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5181 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (k X0 x) x)) ∨ y = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq547 X1 X0 (k X0 x)
       have i₂ := eq5101 (k X0 x) X0
       grind)
    | exact superpose eq5101 eq547
    | (have j1 := eq5101 X0 X0
       grind)
    | exact resolve eq547 eq5101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5101
  have eq5231 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op x (k X0 x))) ∨ y = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5181 X0 X1
       have i₂ := eq1127 x X1 (k X0 x)
       grind)
    | (have i₁ := eq5181 X0 X1
       have i₂ := eq1127 (k X0 x) X1 x
       grind)
    | exact superpose eq1127 eq5181
    | (have j0 := eq5181 X0 X1
       grind)
    | exact resolve eq5181 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5181
  have eq6289 : (k y (σ x)) ≠ (σ (k (τ y) x)) ∨ y = (k (σ x) (σ x)) ∨ (k x x) = (τ y) := by
    first
    | (have i₁ := eq2784
       have i₂ := eq2791 x
       grind)
    | exact superpose eq2791 eq2784
    | (have j1 := eq2791 x
       grind)
    | exact resolve eq2784 eq2791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2784 eq2791
  have eq6291 : (k y (σ x)) ≠ (k (σ (τ y)) (σ x)) ∨ y = (k (σ x) (σ x)) ∨ (k x x) = (τ y) := by
    first
    | (have i₁ := eq6289
       have i₂ := eq15 (τ y) x
       grind)
    | exact superpose eq15 eq6289
    | exact resolve eq6289 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6289
  have eq6307 : (k y (σ x)) ≠ (k y (σ x)) ∨ y = (k (σ x) (σ x)) ∨ (k x x) = (τ y) := by
    first
    | (have i₁ := eq6291
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq6291
    | exact resolve eq6291 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6291
  have eq6308 : y = (k (σ x) (σ x)) ∨ (k x x) = (τ y) := by grind
  clear eq6307
  have eq6318 : y = (τ y) ∨ y = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6308
       have i₂ := eq2642
       grind)
    | exact superpose eq2642 eq6308
    | exact resolve eq6308 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6308
  have eq6342 : y = (σ y) ∨ y = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq11 y
       have i₂ := eq6318
       grind)
    | exact superpose eq6318 eq11
    | exact resolve eq11 eq6318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6318
  have eq6347 : y = (k (σ x) (σ x)) ∨ y = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6342
       have i₂ := eq2664
       grind)
    | exact superpose eq2664 eq6342
    | exact resolve eq6342 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6342
  have eq6348 : y = (k (σ x) (σ x)) := by grind
  clear eq6347
  have eq6353 : y = (σ y) := by
    first
    | (have i₁ := eq2664
       have i₂ := eq6348
       grind)
    | exact superpose eq6348 eq2664
    | exact resolve eq2664 eq6348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2664
  have eq6402 : y = (τ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6353
       grind)
    | exact superpose eq6353 eq10
    | exact resolve eq10 eq6353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6405 : (τ (k y y)) = (M.op y y) := by
    first
    | (have i₁ := eq2810
       have i₂ := eq6402
       grind)
    | exact superpose eq6402 eq2810
    | exact resolve eq2810 eq6402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2810
  have eq6567 : (k y y) = (τ (k y y)) := by
    first
    | (have i₁ := eq6405
       have i₂ := eq136 y
       grind)
    | exact superpose eq136 eq6405
    | exact resolve eq6405 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6405
  have eq6787 : (σ x) = (M.op (k y y) (σ x)) := by
    first
    | (have i₁ := eq157 (σ x)
       have i₂ := eq6348
       grind)
    | exact superpose eq6348 eq157
    | exact resolve eq157 eq6348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6799 : y ≠ y ∨ (k x (σ x)) = (M.op (σ x) x) := by
    first
    | (have i₁ := eq2644 (σ x)
       have i₂ := eq6348
       grind)
    | exact superpose eq6348 eq2644
    | (have j0 := eq2644 (σ x)
       grind)
    | (have r₁ := eq2644 (σ x)
       have r₂ := eq6348
       grind)
    | exact resolve eq2644 eq6348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6800 : y ≠ y ∨ (k (σ x) x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq2645 (σ x)
       have i₂ := eq6348
       grind)
    | exact superpose eq6348 eq2645
    | (have j0 := eq2645 (σ x)
       grind)
    | (have r₁ := eq2645 (σ x)
       have r₂ := eq6348
       grind)
    | exact resolve eq2645 eq6348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6809 : (σ y) = (k (σ (σ x)) (σ (σ x))) := by
    first
    | (have i₁ := eq15 (σ x) (σ x)
       have i₂ := eq6348
       grind)
    | exact superpose eq6348 eq15
    | exact resolve eq15 eq6348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6810 : (k (σ x) x) = (M.op x (σ x)) := by grind
  clear eq6800
  have eq6811 : (k x (σ x)) = (M.op (σ x) x) := by grind
  clear eq6799
  have eq6812 : y = (k (σ (σ x)) (σ (σ x))) := by
    first
    | (have i₁ := eq6809
       have i₂ := eq6353
       grind)
    | exact superpose eq6353 eq6809
    | exact resolve eq6809 eq6353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6809
  have eq6837 : ∀ X0 : G, (τ (k X0 (k y y))) = (k (τ X0) (k y y)) := by
    intro X0
    first
    | (have i₁ := eq29 (k y y) X0
       have i₂ := eq6567
       grind)
    | exact superpose eq6567 eq29
    | exact resolve eq29 eq6567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq7686 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op x (k x (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq547 X0 (σ x) x
       have i₂ := eq6811
       grind)
    | exact superpose eq6811 eq547
    | exact resolve eq547 eq6811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7689 : ∀ X0 : G, (M.op X0 (M.op x (σ x))) = (M.op X0 (k x (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1127 x X0 (σ x)
       have i₂ := eq6811
       grind)
    | exact superpose eq6811 eq1127
    | exact resolve eq1127 eq6811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7690 : ∀ X0 : G, (M.op X0 (k (σ x) x)) = (M.op X0 (k x (σ x))) := by
    intro X0
    first
    | (have i₁ := eq7689 X0
       have i₂ := eq6810
       grind)
    | exact superpose eq6810 eq7689
    | exact resolve eq7689 eq6810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7689
  have eq7707 : (σ (σ x)) = (M.op (k y y) (σ (σ x))) := by
    first
    | (have i₁ := eq157 (σ (σ x))
       have i₂ := eq6812
       grind)
    | exact superpose eq6812 eq157
    | exact resolve eq157 eq6812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7721 : y ≠ y ∨ (k x (σ (σ x))) = (M.op (σ (σ x)) x) := by
    first
    | (have i₁ := eq2644 (σ (σ x))
       have i₂ := eq6812
       grind)
    | exact superpose eq6812 eq2644
    | (have j0 := eq2644 (σ (σ x))
       grind)
    | (have r₁ := eq2644 (σ (σ x))
       have r₂ := eq6812
       grind)
    | exact resolve eq2644 eq6812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2644
  have eq7722 : y ≠ y ∨ (k (σ (σ x)) x) = (M.op x (σ (σ x))) := by
    first
    | (have i₁ := eq2645 (σ (σ x))
       have i₂ := eq6812
       grind)
    | exact superpose eq6812 eq2645
    | (have j0 := eq2645 (σ (σ x))
       grind)
    | (have r₁ := eq2645 (σ (σ x))
       have r₂ := eq6812
       grind)
    | exact resolve eq2645 eq6812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7732 : (k (σ (σ x)) x) = (M.op x (σ (σ x))) := by grind
  clear eq7722
  have eq7733 : (k x (σ (σ x))) = (M.op (σ (σ x)) x) := by grind
  clear eq7721
  have eq7990 : ∀ X0 : G, (M.op X0 (M.op x (σ (σ x)))) = (M.op X0 (k x (σ (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq1127 x X0 (σ (σ x))
       have i₂ := eq7733
       grind)
    | exact superpose eq7733 eq1127
    | exact resolve eq1127 eq7733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7991 : ∀ X0 : G, (M.op X0 (k (σ (σ x)) x)) = (M.op X0 (k x (σ (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq7990 X0
       have i₂ := eq7732
       grind)
    | exact superpose eq7732 eq7990
    | exact resolve eq7990 eq7732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7990
  have eq8560 : (k (k y y) (k y y)) = (τ (k (k y y) (k y y))) := by
    first
    | (have i₁ := eq6837 (k y y)
       have i₂ := eq6567
       grind)
    | exact superpose eq6567 eq6837
    | exact resolve eq6837 eq6567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6567 eq6837
  have eq9394 : (k (σ x) x) = (M.op (k (k (k (σ x) x) (k (σ x) x)) (k (k (σ x) x) (k (σ x) x))) (k x (σ x))) := by
    first
    | (have i₁ := eq157 (k (σ x) x)
       have i₂ := eq7690 (k (k (k (σ x) x) (k (σ x) x)) (k (k (σ x) x) (k (σ x) x)))
       grind)
    | exact superpose eq7690 eq157
    | exact resolve eq157 eq7690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7690
  have eq10115 : ∀ X0 : G, (k X0 x) = (M.op (k (k y y) (k y y)) (M.op (k y y) (k X0 x))) ∨ (k (k (k y y) (k y y)) (k (k y y) (k y y))) = X0 ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq1395 (k y y) (k X0 x) X0
       have i₂ := eq3558 X0
       grind)
    | exact superpose eq3558 eq1395
    | (have j0 := eq1395 (k y y) x X0
       have j1 := eq3558 X0
       grind)
    | exact resolve eq1395 eq3558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395 eq3558
  have eq10313 : ∀ X0 : G, (k X0 x) = (M.op (k (k y y) (k y y)) (k X0 x)) ∨ (k (k (k y y) (k y y)) (k (k y y) (k y y))) = X0 ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq10115 X0
       have i₂ := eq1157 y (k (k y y) (k y y)) (k X0 x)
       grind)
    | exact superpose eq1157 eq10115
    | (have j0 := eq10115 X0
       grind)
    | exact resolve eq10115 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10115
  have eq10383 : ∀ X0 : G, y = X0 ∨ (k X0 x) = (M.op (k (k y y) (k y y)) (k X0 x)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq10313 X0
       have i₂ := eq4094
       grind)
    | exact superpose eq4094 eq10313
    | (have j0 := eq10313 X0
       grind)
    | exact resolve eq10313 eq4094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4094 eq10313
  have eq10384 : ∀ X0 : G, y = X0 ∨ (k X0 x) = (M.op (k (k y y) (k y y)) (k X0 x)) := by
    intro X0
    first
    | (have j0 := eq10383 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10383
  have eq14635 : (k (k (σ x) (σ x)) (k (σ x) (σ x))) = (k (k x (σ x)) (k x (σ x))) := by
    first
    | (have i₁ := eq167 (σ x) x
       have i₂ := eq6811
       grind)
    | exact superpose eq6811 eq167
    | exact resolve eq167 eq6811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6811
  have eq14670 : (k (k x x) (k x x)) = (k (k (σ x) x) (k (σ x) x)) := by
    first
    | (have i₁ := eq167 x (σ x)
       have i₂ := eq6810
       grind)
    | exact superpose eq6810 eq167
    | exact resolve eq167 eq6810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14714 : ∀ X0 X1 : G, (σ (k (k X0 X0) (k X0 X0))) = (k (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq167 X0 X1
       grind)
    | exact superpose eq167 eq15
    | exact resolve eq15 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq14729 : ∀ X0 X1 : G, (k (σ (k X0 X0)) (σ (k X0 X0))) = (k (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14714 X0 X1
       have i₂ := eq15 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq15 eq14714
    | exact resolve eq14714 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14714
  have eq14748 : (k y y) = (k (k (σ x) x) (k (σ x) x)) := by
    first
    | (have i₁ := eq14670
       have i₂ := eq2642
       grind)
    | exact superpose eq2642 eq14670
    | exact resolve eq14670 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14670
  have eq14769 : (k y y) = (k (k x (σ x)) (k x (σ x))) := by
    first
    | (have i₁ := eq14635
       have i₂ := eq6348
       grind)
    | exact superpose eq6348 eq14635
    | exact resolve eq14635 eq6348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14635
  have eq14775 : ∀ X0 X1 : G, (k (k (σ X0) (σ X0)) (k (σ X0) (σ X0))) = (k (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14729 X1 X1
       have i₂ := eq15 X1 X1
       grind)
    | exact superpose eq15 eq14729
    | exact resolve eq14729 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14729
  have eq14791 : (k (σ x) x) = (M.op (k (k y y) (k y y)) (k x (σ x))) := by
    first
    | (have i₁ := eq9394
       have i₂ := eq14748
       grind)
    | exact superpose eq14748 eq9394
    | exact resolve eq9394 eq14748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9394 eq14748
  have eq14921 : (k x (σ x)) = (M.op (k (k y y) (k y y)) (k x (σ x))) := by
    first
    | (have i₁ := eq157 (k x (σ x))
       have i₂ := eq14769
       grind)
    | exact superpose eq14769 eq157
    | exact resolve eq157 eq14769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq14769
  have eq14970 : (k x (σ x)) = (k (σ x) x) := by
    first
    | (have i₁ := eq14791
       have i₂ := eq14921
       grind)
    | exact superpose eq14921 eq14791
    | exact resolve eq14791 eq14921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14791 eq14921
  have eq14979 : (k x (σ x)) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq6810
       have i₂ := eq14970
       grind)
    | exact superpose eq14970 eq6810
    | exact resolve eq6810 eq14970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6810 eq14970
  have eq16451 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (k (k y y) (k y y)) (M.op (k y y) (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq1408 (k y y) (σ x) X0
       have i₂ := eq6787
       grind)
    | exact superpose eq6787 eq1408
    | exact resolve eq1408 eq6787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16452 : ∀ X0 : G, (M.op (σ (σ x)) X0) = (M.op (k (k y y) (k y y)) (M.op (k y y) (M.op (σ (σ x)) X0))) := by
    intro X0
    first
    | (have i₁ := eq1408 (k y y) (σ (σ x)) X0
       have i₂ := eq7707
       grind)
    | exact superpose eq7707 eq1408
    | exact resolve eq1408 eq7707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16456 : ∀ X0 : G, (M.op x X0) = (M.op (k (k y y) (k y y)) (M.op (k y y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq1408 (k y y) x X0
       have i₂ := eq2647
       grind)
    | exact superpose eq2647 eq1408
    | exact resolve eq1408 eq2647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16504 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op X3 (M.op X2 (M.op (k X0 X0) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq547 X3 (M.op X0 X1) X2
       have i₂ := eq1408 X0 X1 X2
       grind)
    | exact superpose eq1408 eq547
    | exact resolve eq547 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408
  have eq16619 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op X3 (M.op X2 (M.op X0 (M.op (k X0 X0) (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16504 X0 X1 X2 X3
       have i₂ := eq1128 (k X0 X0) (M.op X1 X2) X2 X0
       grind)
    | (have i₁ := eq16504 X0 X1 X2 X3
       have i₂ := eq1128 X0 (M.op X1 X2) X2 (k X0 X0)
       grind)
    | exact superpose eq1128 eq16504
    | exact resolve eq16504 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16504
  have eq16667 : ∀ X0 : G, (M.op x X0) = (M.op (k (k y y) (k y y)) (M.op x (M.op (k y y) X0))) := by
    intro X0
    first
    | (have i₁ := eq16456 X0
       have i₂ := eq1128 (k y y) X0 (k (k y y) (k y y)) x
       grind)
    | (have i₁ := eq16456 X0
       have i₂ := eq1128 x X0 (k (k y y) (k y y)) (k y y)
       grind)
    | exact superpose eq1128 eq16456
    | exact resolve eq16456 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16456
  have eq16671 : ∀ X0 : G, (M.op (σ (σ x)) X0) = (M.op (k (k y y) (k y y)) (M.op (σ (σ x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq16452 X0
       have i₂ := eq1157 y (k (k y y) (k y y)) (M.op (σ (σ x)) X0)
       grind)
    | exact superpose eq1157 eq16452
    | exact resolve eq16452 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16452
  have eq16672 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (k (k y y) (k y y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16451 X0
       have i₂ := eq1157 y (k (k y y) (k y y)) (M.op (σ x) X0)
       grind)
    | exact superpose eq1157 eq16451
    | exact resolve eq16451 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16451
  have eq16758 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op X3 (M.op X2 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16619 X0 X1 X2 X3
       have i₂ := eq1157 X0 X0 (M.op X1 X2)
       grind)
    | exact superpose eq1157 eq16619
    | exact resolve eq16619 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16619
  have eq16797 : ∀ X0 : G, (M.op x X0) = (M.op (k (k y y) (k y y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq16667 X0
       have i₂ := eq1157 y x X0
       grind)
    | exact superpose eq1157 eq16667
    | exact resolve eq16667 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16667
  have eq19808 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op X1 (σ (σ x))))) = (M.op X0 (M.op X1 (k (σ (σ x)) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq1128 x (σ (σ x)) X0 X1
       have i₂ := eq7732
       grind)
    | exact superpose eq7732 eq1128
    | exact resolve eq1128 eq7732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7732
  have eq20136 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k x (σ (σ x))))) = (M.op X0 (M.op x (M.op X1 (σ (σ x))))) := by
    intro X0 X1
    first
    | (have i₁ := eq19808 X0 X1
       have i₂ := eq7991 X1
       grind)
    | exact superpose eq7991 eq19808
    | exact resolve eq19808 eq7991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7991 eq19808
  have eq20779 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (k (k y y) (k y y)) (M.op (k y y) (M.op X0 (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq1266 (k y y) (σ x) X0
       have i₂ := eq6787
       grind)
    | exact superpose eq6787 eq1266
    | exact resolve eq1266 eq6787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6787
  have eq20780 : ∀ X0 : G, (M.op (σ (σ x)) X0) = (M.op (k (k y y) (k y y)) (M.op (k y y) (M.op X0 (σ (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq1266 (k y y) (σ (σ x)) X0
       have i₂ := eq7707
       grind)
    | exact superpose eq7707 eq1266
    | exact resolve eq1266 eq7707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266 eq7707
  have eq21258 : ∀ X0 : G, (M.op (σ (σ x)) X0) = (M.op (k (k y y) (k y y)) (M.op X0 (σ (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq20780 X0
       have i₂ := eq1157 y (k (k y y) (k y y)) (M.op X0 (σ (σ x)))
       grind)
    | exact superpose eq1157 eq20780
    | exact resolve eq20780 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20780
  have eq21259 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (k (k y y) (k y y)) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq20779 X0
       have i₂ := eq1157 y (k (k y y) (k y y)) (M.op X0 (σ x))
       grind)
    | exact superpose eq1157 eq20779
    | exact resolve eq20779 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157 eq20779
  have eq21524 : (k x (σ (σ x))) = (M.op (k (k y y) (k y y)) (M.op x (σ (σ x)))) := by
    first
    | (have i₁ := eq7733
       have i₂ := eq21258 x
       grind)
    | exact superpose eq21258 eq7733
    | exact resolve eq7733 eq21258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7733
  have eq21532 : (σ (M.op x y)) ≠ (M.op (k (k y y) (k y y)) (M.op y (σ x))) := by
    first
    | (have i₁ := eq2719
       have i₂ := eq21259 y
       grind)
    | exact superpose eq21259 eq2719
    | exact resolve eq2719 eq21259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2719 eq21259
  have eq21712 : (k x (σ (σ x))) = (M.op x (σ (σ x))) := by
    first
    | (have i₁ := eq21524
       have i₂ := eq16797 (σ (σ x))
       grind)
    | exact superpose eq16797 eq21524
    | exact resolve eq21524 eq16797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21524
  have eq21714 : (σ (M.op x y)) ≠ (M.op (k (k y y) (k y y)) (σ x)) := by
    first
    | (have i₁ := eq21532
       have i₂ := eq2650 (k (k y y) (k y y)) (σ x)
       grind)
    | exact superpose eq2650 eq21532
    | exact resolve eq21532 eq2650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21532
  have eq25820 : ∀ X0 : G, (M.op (k (k y y) (k y y)) X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq842 (k (k y y) (k y y)) X0 x
       have i₂ := eq16797 (M.op x X0)
       grind)
    | exact superpose eq16797 eq842
    | exact resolve eq842 eq16797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842 eq16797
  have eq25886 : ∀ X0 : G, (M.op (σ (σ x)) X0) = (M.op x (M.op x (M.op X0 (σ (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq21258 X0
       have i₂ := eq25820 (M.op X0 (σ (σ x)))
       grind)
    | exact superpose eq25820 eq21258
    | exact resolve eq21258 eq25820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21258
  have eq25894 : ∀ X0 : G, (M.op (σ (σ x)) X0) = (M.op x (M.op x (M.op (σ (σ x)) X0))) := by
    intro X0
    first
    | (have i₁ := eq16671 X0
       have i₂ := eq25820 (M.op (σ (σ x)) X0)
       grind)
    | exact superpose eq25820 eq16671
    | exact resolve eq16671 eq25820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16671
  have eq25895 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x (M.op x (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq16672 X0
       have i₂ := eq25820 (M.op (σ x) X0)
       grind)
    | exact superpose eq25820 eq16672
    | exact resolve eq16672 eq25820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16672
  have eq25901 : (σ (M.op x y)) ≠ (M.op x (M.op x (σ x))) := by
    first
    | (have i₁ := eq21714
       have i₂ := eq25820 (σ x)
       grind)
    | exact superpose eq25820 eq21714
    | exact resolve eq21714 eq25820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21714
  have eq25925 : ∀ X0 : G, (k X0 x) = (M.op x (M.op x (k X0 x))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq10384 X0
       have i₂ := eq25820 (k X0 x)
       grind)
    | exact superpose eq25820 eq10384
    | (have j0 := eq10384 X0
       grind)
    | exact resolve eq10384 eq25820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10384 eq25820
  have eq26031 : (σ (M.op x y)) ≠ (M.op x (k x (σ x))) := by
    first
    | (have i₁ := eq25901
       have i₂ := eq14979
       grind)
    | exact superpose eq14979 eq25901
    | exact resolve eq25901 eq14979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25901
  have eq29003 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq25895 (M.op X0 (σ x))
       have i₂ := eq547 x X0 (σ x)
       grind)
    | exact superpose eq547 eq25895
    | exact resolve eq25895 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25895
  have eq31206 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ y = X0 ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq5231 X0 x
       have i₂ := eq25925 X0
       grind)
    | exact superpose eq25925 eq5231
    | (have j0 := eq5231 X0 x
       have j1 := eq25925 X0
       grind)
    | exact resolve eq5231 eq25925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5231 eq25925
  have eq31235 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq31206 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31206
  have eq31385 : ∀ X0 X1 : G, (M.op X0 X1) = y ∨ (M.op x (M.op X1 X0)) = (k (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq1127 X0 x X1
       have i₂ := eq31235 (M.op X0 X1)
       grind)
    | exact superpose eq31235 eq1127
    | (have j1 := eq31235 (M.op X0 X1)
       grind)
    | exact resolve eq1127 eq31235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31235
  have eq62116 : ∀ X0 : G, (M.op (σ (σ x)) X0) = (M.op x (M.op X0 (M.op x (σ (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq1128 x (σ (σ x)) x X0
       have i₂ := eq25886 X0
       grind)
    | exact superpose eq25886 eq1128
    | exact resolve eq1128 eq25886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128 eq25886
  have eq62168 : ∀ X0 : G, (M.op (σ (σ x)) X0) = (M.op x (M.op X0 (k x (σ (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq62116 X0
       have i₂ := eq21712
       grind)
    | exact superpose eq21712 eq62116
    | exact resolve eq62116 eq21712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21712 eq62116
  have eq65120 : (M.op (σ (σ x)) (k x (σ (σ x)))) = (M.op x (k (k x (σ (σ x))) (k x (σ (σ x))))) := by
    first
    | (have i₁ := eq62168 (k x (σ (σ x)))
       have i₂ := eq136 (k x (σ (σ x)))
       grind)
    | exact superpose eq136 eq62168
    | exact resolve eq62168 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62168
  have eq65413 : (M.op x y) = (M.op (σ (σ x)) (k x (σ (σ x)))) := by
    first
    | (have i₁ := eq65120
       have i₂ := eq2658 x (k x (σ (σ x)))
       grind)
    | exact superpose eq2658 eq65120
    | exact resolve eq65120 eq2658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2658 eq65120
  have eq147658 : ∀ X0 X1 : G, y ≠ (k X0 X0) ∨ (M.op x (k X0 X0)) = (k (k X0 X0) x) ∨ (M.op X1 X0) = (M.op X1 (k (k X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2645 (k X0 X0)
       have i₂ := eq1206 X0 X1
       grind)
    | exact superpose eq1206 eq2645
    | (have j0 := eq2645 X0
       have j1 := eq1206 X0 X1
       grind)
    | exact resolve eq2645 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206 eq2645
  have eq147724 : ∀ X0 X1 : G, y ≠ (k X0 X0) ∨ (M.op x y) = (k y x) ∨ (M.op X1 X0) = (M.op X1 (k y X0)) := by
    intro X0 X1
    first
    | (have j0 := eq147658 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147658
  have eq147745 : ∀ X0 X1 : G, (M.op x y) = (k y x) ∨ (M.op X1 X0) = (M.op X1 (k y X0)) := by
    intro X0 X1
    first
    | (have j0 := eq147724 X0 X1
       have j1 := eq2836 X0 X1
       grind)
    | (have r₁ := eq147724 X0 X1
       have r₂ := eq2836 X0 X1
       grind)
    | exact resolve eq147724 eq2836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2836 eq147724
  have eq147886 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op X0 (k y x)) ∨ (M.op X1 X2) = (M.op X1 (k y X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2653 X0 x
       have i₂ := eq147745 X2 X1
       grind)
    | exact superpose eq147745 eq2653
    | (have j1 := eq147745 x X0
       grind)
    | exact resolve eq2653 eq147745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147745
  have eq147931 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (k y x)) := by
    intro X0
    first
    | (have j0 := eq147886 X0 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147886
  have eq148404 : ∀ X0 X1 : G, (M.op X1 (M.op X0 x)) = (M.op X1 (M.op (k y x) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1127 (k y x) X1 X0
       have i₂ := eq147931 X0
       grind)
    | exact superpose eq147931 eq1127
    | exact resolve eq1127 eq147931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147931
  have eq150823 : ∀ X0 X1 : G, (M.op X0 (M.op (k y x) X1)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1127 X1 X0 x
       have i₂ := eq148404 X1 X0
       grind)
    | exact superpose eq148404 eq1127
    | exact resolve eq1127 eq148404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180781 : y = (M.op x y) ∨ (k (M.op x y) x) = (M.op x (M.op (k x (σ (σ x))) (σ (σ x)))) := by
    first
    | (have i₁ := eq31385 (σ (σ x)) (k x (σ (σ x)))
       have i₂ := eq65413
       grind)
    | exact superpose eq65413 eq31385
    | (have j0 := eq31385 x y
       grind)
    | exact resolve eq31385 eq65413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31385 eq65413
  have eq182217 : (M.op x (M.op (σ (σ x)) (k x (σ (σ x))))) = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq180781
       have i₂ := eq1127 (σ (σ x)) x (k x (σ (σ x)))
       grind)
    | (have i₁ := eq180781
       have i₂ := eq1127 (k x (σ (σ x))) x (σ (σ x))
       grind)
    | exact superpose eq1127 eq180781
    | exact resolve eq180781 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180781
  have eq182772 : (k (M.op x y) x) = (M.op x (M.op x (M.op (σ (σ x)) (σ (σ x))))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq182217
       have i₂ := eq20136 x (σ (σ x))
       grind)
    | exact superpose eq20136 eq182217
    | exact resolve eq182217 eq20136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20136 eq182217
  have eq183081 : (M.op (σ (σ x)) (σ (σ x))) = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq182772
       have i₂ := eq25894 (σ (σ x))
       grind)
    | exact superpose eq25894 eq182772
    | exact resolve eq182772 eq25894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25894 eq182772
  have eq183229 : (k (σ (σ x)) (σ (σ x))) = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq183081
       have i₂ := eq136 (σ (σ x))
       grind)
    | exact superpose eq136 eq183081
    | exact resolve eq183081 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq183081
  have eq183334 : y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq183229
       have i₂ := eq6812
       grind)
    | exact superpose eq6812 eq183229
    | exact resolve eq183229 eq6812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6812 eq183229
  have eq183523 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15 (M.op x y) x
       have i₂ := eq183334
       grind)
    | exact superpose eq183334 eq15
    | exact resolve eq15 eq183334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183334
  have eq183608 : y = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq183523
       have i₂ := eq6353
       grind)
    | exact superpose eq6353 eq183523
    | exact resolve eq183523 eq6353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183523
  have eq183783 : (σ (M.op x y)) = (M.op (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) (M.op (σ x) y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1371 (σ (M.op x y)) (σ x)
       have i₂ := eq183608
       grind)
    | exact superpose eq183608 eq1371
    | (have j0 := eq1371 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq1371 eq183608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371 eq183608
  have eq183829 : (σ (M.op x y)) = (M.op (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) (M.op y (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq183783
       have i₂ := eq1127 y (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) (σ x)
       grind)
    | (have i₁ := eq183783
       have i₂ := eq1127 (σ x) (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) y
       grind)
    | exact superpose eq1127 eq183783
    | exact resolve eq183783 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127 eq183783
  have eq183873 : (σ (M.op x y)) = (M.op (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq183829
       have i₂ := eq2650 (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) (σ x)
       grind)
    | exact superpose eq2650 eq183829
    | exact resolve eq183829 eq2650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2650 eq183829
  have eq183908 : (σ (M.op x y)) = (M.op (k (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (k (σ x) (σ x)) (k (σ x) (σ x)))) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq183873
       have i₂ := eq14775 x y
       grind)
    | exact superpose eq14775 eq183873
    | exact resolve eq183873 eq14775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14775 eq183873
  have eq183931 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq183908
       have i₂ := eq1093 (σ x) (σ x)
       grind)
    | exact superpose eq1093 eq183908
    | exact resolve eq183908 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093 eq183908
  have eq183942 : (σ (M.op x y)) = (M.op x (M.op x (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq183931
       have i₂ := eq29003 (σ x)
       grind)
    | exact superpose eq29003 eq183931
    | exact resolve eq183931 eq29003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29003 eq183931
  have eq183948 : (σ (M.op x y)) = (M.op x (k x (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq183942
       have i₂ := eq14979
       grind)
    | exact superpose eq14979 eq183942
    | exact resolve eq183942 eq14979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183942
  have eq183952 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq183948
       have r₂ := eq26031
       grind)
    | exact resolve eq183948 eq26031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183948
  have eq183956 : y = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq183952
       have i₂ := eq6348
       grind)
    | exact superpose eq6348 eq183952
    | exact resolve eq183952 eq6348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6348 eq183952
  have eq185558 : (M.op x y) = (τ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq183956
       grind)
    | exact superpose eq183956 eq10
    | exact resolve eq10 eq183956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183956
  have eq185607 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq185558
       have i₂ := eq6402
       grind)
    | exact superpose eq6402 eq185558
    | exact resolve eq185558 eq6402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6402 eq185558
  have eq185608 : y = (M.op x y) := by grind
  clear eq185607
  have eq185653 : (σ y) ≠ (M.op x (k x (σ x))) := by
    first
    | (have i₁ := eq26031
       have i₂ := eq185608
       grind)
    | exact superpose eq185608 eq26031
    | exact resolve eq26031 eq185608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26031
  have eq186640 : y ≠ (M.op x (k x (σ x))) := by
    first
    | (have i₁ := eq185653
       have i₂ := eq6353
       grind)
    | exact superpose eq6353 eq185653
    | exact resolve eq185653 eq6353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6353 eq185653
  have eq187061 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq2653 X0 x
       have i₂ := eq185608
       grind)
    | exact superpose eq185608 eq2653
    | exact resolve eq2653 eq185608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2653
  have eq187105 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op X1 y))) = (M.op X0 (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq16758 X1 x y X0
       have i₂ := eq185608
       grind)
    | exact superpose eq185608 eq16758
    | exact resolve eq16758 eq185608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16758 eq185608
  have eq187111 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq187105 X0 X1
       have i₂ := eq547 X0 X1 y
       grind)
    | exact superpose eq547 eq187105
    | exact resolve eq187105 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq187105
  have eq189490 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (M.op (k X0 X0) x) := by
    intro X0
    first
    | (have i₁ := eq2652 X0
       have i₂ := eq187061 (k X0 X0)
       grind)
    | exact superpose eq187061 eq2652
    | exact resolve eq2652 eq187061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2652 eq187061
  have eq191957 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (k y x) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq148404 X0 X1
       have i₂ := eq187111 X1 X0
       grind)
    | exact superpose eq187111 eq148404
    | exact resolve eq148404 eq187111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148404 eq187111
  have eq193099 : x = (k (k y y) (k y y)) := by
    first
    | (have i₁ := eq2647
       have i₂ := eq189490 y
       grind)
    | exact superpose eq189490 eq2647
    | exact resolve eq2647 eq189490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647 eq189490
  have eq194798 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq150823 X0 X1
       have i₂ := eq191957 X1 X0
       grind)
    | exact superpose eq191957 eq150823
    | exact resolve eq150823 eq191957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150823 eq191957
  have eq197317 : x = (τ x) := by
    first
    | (have i₁ := eq8560
       have i₂ := eq193099
       grind)
    | exact superpose eq193099 eq8560
    | exact resolve eq8560 eq193099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8560 eq193099
  have eq199791 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (k x (σ x))) := by
    intro X0
    first
    | (have i₁ := eq7686 X0
       have i₂ := eq194798 X0 (k x (σ x))
       grind)
    | exact superpose eq194798 eq7686
    | exact resolve eq7686 eq194798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7686 eq194798
  have eq206305 : y ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq186640
       have i₂ := eq199791 x
       grind)
    | exact superpose eq199791 eq186640
    | exact resolve eq186640 eq199791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186640 eq199791
  have eq210759 : y ≠ (k x (σ x)) := by
    first
    | (have i₁ := eq206305
       have i₂ := eq14979
       grind)
    | exact superpose eq14979 eq206305
    | exact resolve eq206305 eq14979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14979 eq206305
  have eq225829 : x = (σ x) := by
    first
    | (have i₁ := eq11 x
       have i₂ := eq197317
       grind)
    | exact superpose eq197317 eq11
    | exact resolve eq11 eq197317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197317
  have eq227069 : y ≠ (k x x) := by
    first
    | (have i₁ := eq210759
       have i₂ := eq225829
       grind)
    | exact superpose eq225829 eq210759
    | exact resolve eq210759 eq225829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210759 eq225829
  have eq230758 : False := by grind
  exact eq230758

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_y_pxy_pyx_pxy_Equation2685 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X0) X1) (M.op (M.op X1 X2) (M.op X0 X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 X2) (M.op X0 X2))
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq56
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq56
    | exact resolve eq56 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq59 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq65 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq9
    | exact resolve eq9 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq9
    | exact resolve eq9 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X1
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0 (σ X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq65
    | exact resolve eq65 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq93 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq60 (M.op X0 X0)
       grind)
    | exact superpose eq60 eq83
    | exact resolve eq83 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq139 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0 (τ X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq75
    | exact resolve eq75 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq151 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op (M.op X0 X0) (M.op X0 X0))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq139 X0
       have i₂ := eq59 (M.op X0 X0)
       grind)
    | exact superpose eq59 eq139
    | exact resolve eq139 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq139
  have eq238 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 x X2
       have i₂ := eq53 X0 x X2 X1
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X1)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0
       have i₂ := eq53 X0 X0 X0 X1
       grind)
    | exact superpose eq53 eq151
    | exact resolve eq151 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq254 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X3) (M.op X1 X3)) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq53 (M.op X0 X1) X3 X1 x
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (M.op X0 X1) X3)) = (M.op (M.op X2 X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq238 (M.op (M.op X2 X3) (M.op (M.op X0 X1) X3)) X0 X1
       have i₂ := eq9 X2 X3 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq238
    | exact resolve eq238 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op X2 (M.op X3 (M.op X0 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq238 (M.op (M.op X2 (M.op X3 (M.op X0 X1))) X3) X0 X1
       have i₂ := eq238 X2 X3 (M.op X0 X1)
       grind)
    | exact superpose eq238 eq238
    | exact resolve eq238 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq238 (M.op X1 (M.op (M.op X0 X2) X0)) X0 X2
       have i₂ := eq238 X1 (M.op X0 X2) X0
       grind)
    | exact superpose eq238 eq238
    | exact resolve eq238 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 (M.op X1 (M.op X0 X1))) X1 X0
       have i₂ := eq238 X2 X1 (M.op X0 X1)
       grind)
    | exact superpose eq238 eq9
    | exact resolve eq9 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X1 X2)) X0) = (M.op (M.op X3 (M.op X4 (M.op (M.op X0 X1) X2))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X3 (M.op X1 X2) (M.op (M.op X0 X1) X2) X4
       have i₂ := eq254 X0 X1 X2
       grind)
    | exact superpose eq254 eq53
    | exact resolve eq53 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) (M.op (M.op X1 X2) X4)) = (M.op (M.op X3 X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X3 X4 (M.op X1 X2) (M.op (M.op X0 X1) X2)
       have i₂ := eq254 X0 X1 X2
       grind)
    | exact superpose eq254 eq53
    | exact resolve eq53 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op (M.op X0 X1) X2)) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq354 X0 X1 X2 X3 x
       have i₂ := eq280 X1 X2 X3 x
       grind)
    | exact superpose eq280 eq354
    | exact resolve eq354 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq357 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X1 X2)) X0) = (M.op (M.op X3 (M.op X0 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq353 X0 X1 X2 X3 x
       have i₂ := eq281 (M.op X0 X1) X2 X3 x
       grind)
    | exact superpose eq281 eq353
    | exact resolve eq353 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq381 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq285 (M.op X0 X1) X2 (M.op (M.op X0 X1) X1)
       have i₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq285
    | exact resolve eq285 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X0) X3)) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq285 X0 (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X0) X3)) X1
       have i₂ := eq9 X2 X3 (M.op (M.op X0 X1) X0)
       grind)
    | exact superpose eq9 eq285
    | exact resolve eq285 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op (M.op (M.op X1 X0) X1) X3)) X0) X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq238 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq285 X1 (M.op X2 (M.op (M.op (M.op X1 X0) X1) X3)) X0
       grind)
    | exact superpose eq285 eq238
    | exact resolve eq238 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X1 X0) X1)) X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq410 X0 X1 X2 X3
       have i₂ := eq357 (M.op (M.op X1 X0) X1) X3 X0 X2
       grind)
    | (have i₁ := eq410 X0 X1 X3 X2
       have i₂ := eq357 X0 (M.op (M.op X1 X0) X1) X2 X3
       grind)
    | exact superpose eq357 eq410
    | exact resolve eq410 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq429 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X3 X1)) (M.op (M.op X0 X1) X0)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq388 X0 X1 X2 X3
       have i₂ := eq357 (M.op (M.op X0 X1) X0) X3 X1 (M.op X2 X3)
       grind)
    | (have i₁ := eq388 X0 X0 X2 X2
       have i₂ := eq357 X0 (M.op (M.op X0 X0) X0) X2 (M.op X2 X2)
       grind)
    | exact superpose eq357 eq388
    | exact resolve eq388 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq435 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X2 (M.op X3 X0)) X0) X3) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq415 X0 x X2 X3
       have i₂ := eq285 x (M.op X2 (M.op X3 X0)) X0
       grind)
    | exact superpose eq285 eq415
    | exact resolve eq415 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq441 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X3 X1)) X1) = X2 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq429 x X1 X2 X3
       have i₂ := eq285 x (M.op (M.op X2 X3) (M.op X3 X1)) X1
       grind)
    | exact superpose eq285 eq429
    | exact resolve eq429 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285 eq429
  have eq524 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq381 (M.op (M.op X0 X1) X2) (M.op X1 X2) X3
       have i₂ := eq254 X0 X1 X2
       grind)
    | exact superpose eq254 eq381
    | exact resolve eq381 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq381 (M.op X1 (M.op X0 X0)) X0 X2
       have i₂ := eq238 X1 X0 X0
       grind)
    | exact superpose eq238 eq381
    | exact resolve eq381 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X0)) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq292 (M.op X1 X0) X0 X2
       have i₂ := eq381 X1 X0 X0
       grind)
    | exact superpose eq381 eq292
    | exact resolve eq292 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 (M.op X2 X1)
       have i₂ := eq381 X2 X1 (M.op X0 X1)
       grind)
    | exact superpose eq381 eq9
    | exact resolve eq9 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) X1) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X1 (τ X0))
       have i₂ := eq381 X1 (τ X0) (τ (M.op X0 X0))
       grind)
    | exact superpose eq381 eq76
    | exact resolve eq76 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq643 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq435 X1 (M.op (M.op X0 X2) X1) X2
       have i₂ := eq254 X0 X2 X1
       grind)
    | exact superpose eq254 eq435
    | exact resolve eq435 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq654 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq238 (M.op X0 (M.op X1 (M.op X1 X2))) X1 X2
       have i₂ := eq435 (M.op X1 X2) X0 X1
       grind)
    | exact superpose eq435 eq238
    | exact resolve eq238 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X0)) = (M.op X3 (M.op (M.op X0 (M.op X2 X1)) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq292 (M.op (M.op X0 (M.op X2 X1)) X1) X2 X3
       have i₂ := eq435 X1 X0 X2
       grind)
    | exact superpose eq435 eq292
    | exact resolve eq292 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 (M.op (M.op X2 X3) X1)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq238 (M.op (M.op X0 (M.op (M.op X2 X3) X1)) X1) X2 X3
       have i₂ := eq435 X1 X0 (M.op X2 X3)
       grind)
    | exact superpose eq435 eq238
    | exact resolve eq238 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq435
  have eq687 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 (M.op X2 (M.op X3 X1))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq672 X0 X1 X2 X3
       have i₂ := eq524 X2 X3 X1 X0
       grind)
    | (have i₁ := eq672 X3 (M.op X1 X2) X2 X3
       have i₂ := eq524 (M.op X2 X3) X1 X2 X3
       grind)
    | exact superpose eq524 eq672
    | exact resolve eq672 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq689 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X0)) = (M.op X3 (M.op X1 (M.op X0 (M.op X2 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq670 X0 X1 X2 X3
       have i₂ := eq543 X1 (M.op X0 (M.op X2 X1)) X3
       grind)
    | (have i₁ := eq670 X0 X1 X2 X3
       have i₂ := eq543 (M.op X0 (M.op X2 X1)) X1 X3
       grind)
    | exact superpose eq543 eq670
    | exact resolve eq670 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq670
  have eq726 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq687 X0 X1 X2 X3
       have i₂ := eq357 X1 X2 (M.op X3 X1) X0
       grind)
    | (have i₁ := eq687 X3 X2 X0 X3
       have i₂ := eq357 X0 (M.op X3 X2) X2 X3
       grind)
    | exact superpose eq357 eq687
    | exact resolve eq687 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq926 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X2) = (M.op (M.op X0 X3) (M.op (M.op X1 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X3 (M.op X1 X1) X2
       have i₂ := eq533 X1 X2 X0
       grind)
    | exact superpose eq533 eq53
    | exact resolve eq53 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq949 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq441 (M.op X2 X2) X0 X1
       have i₂ := eq533 X2 X1 (M.op X0 X1)
       grind)
    | exact superpose eq533 eq441
    | exact resolve eq441 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq981 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq926 X0 X2 X1 x
       have i₂ := eq280 X2 X2 X0 x
       grind)
    | exact superpose eq280 eq926
    | exact resolve eq926 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq1407 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1549 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0)))) (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq561 X2 X1 (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0)))
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq561
    | exact resolve eq561 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1550 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq561 X2 X1 (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq561
    | exact resolve eq561 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1573 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X0 X2)) X1) = (M.op (M.op X3 (M.op X4 (M.op (M.op X1 X2) X0))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X3 (M.op X0 X2) (M.op (M.op X1 X2) X0) X4
       have i₂ := eq561 X1 X2 X0
       grind)
    | exact superpose eq561 eq53
    | exact resolve eq53 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1593 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X1 X2)) X0) = (M.op (M.op X3 (M.op X0 X2)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1573 X1 X0 X2 X3 x
       have i₂ := eq281 (M.op X0 X2) X1 X3 x
       grind)
    | exact superpose eq281 eq1573
    | exact resolve eq1573 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq1573
  have eq1597 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (M.op (τ X0) (τ (M.op X0 X0)))) (M.op X1 (τ X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1550 X0 X1 X2
       have i₂ := eq357 (τ X0) (τ (M.op X0 X0)) (M.op X1 (τ X0)) (M.op X2 X1)
       grind)
    | (have i₁ := eq1550 X0 X1 X2
       have i₂ := eq357 (τ (M.op X0 X0)) (M.op X1 (τ X0)) (τ X0) (M.op X2 X1)
       grind)
    | exact superpose eq357 eq1550
    | exact resolve eq1550 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550
  have eq1598 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (M.op (σ X0) (σ (M.op X0 X0)))) (M.op X1 (σ X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1549 X0 X1 X2
       have i₂ := eq357 (σ X0) (σ (M.op X0 X0)) (M.op X1 (σ X0)) (M.op X2 X1)
       grind)
    | (have i₁ := eq1549 X0 X1 X2
       have i₂ := eq357 (σ (M.op X0 X0)) (M.op X1 (σ X0)) (σ X0) (M.op X2 X1)
       grind)
    | exact superpose eq357 eq1549
    | exact resolve eq1549 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549
  have eq1632 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (τ (M.op X0 X0))) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1597 X0 X1 X2
       have i₂ := eq726 (M.op X2 X1) (τ X0) (τ (M.op X0 X0)) X1
       grind)
    | exact superpose eq726 eq1597
    | exact resolve eq1597 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597
  have eq1633 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (σ (M.op X0 X0))) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1598 X0 X1 X2
       have i₂ := eq726 (M.op X2 X1) (σ X0) (σ (M.op X0 X0)) X1
       grind)
    | exact superpose eq726 eq1598
    | exact resolve eq1598 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq1598
  have eq1696 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X2) X3) = (M.op (M.op (M.op X1 X2) X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq643 (M.op X1 X2) X3 X0
       have i₂ := eq643 X1 X2 X0
       grind)
    | (have i₁ := eq643 (M.op X1 X2) X3 X0
       have i₂ := eq643 X1 X0 X2
       grind)
    | exact superpose eq643 eq643
    | exact resolve eq643 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1812 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq654 X2 X0 (M.op X1 X1)
       have i₂ := eq533 X1 X0 X0
       grind)
    | exact superpose eq533 eq654
    | exact resolve eq654 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq654
  have eq2170 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (M.op (σ X0) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq981 (σ X0) X1 (σ X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq981
    | exact resolve eq981 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq2385 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X1 X1))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0
       have i₂ := eq1812 X1 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq93 X0
       have i₂ := eq1812 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq1812 eq93
    | exact resolve eq93 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq1812
  have eq2737 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op X1 X0) X2) (τ (M.op X3 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1632 X3 X0 (M.op X1 X2)
       have i₂ := eq643 X1 X2 X0
       grind)
    | (have i₁ := eq1632 X3 X0 (M.op X1 X2)
       have i₂ := eq643 X1 X0 X2
       grind)
    | exact superpose eq643 eq1632
    | exact resolve eq1632 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq2842 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X1 (σ (M.op X3 X3))) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1633 X3 (M.op X0 X2) (M.op (M.op X1 X2) X0)
       have i₂ := eq561 X1 X2 X0
       grind)
    | exact superpose eq561 eq1633
    | exact resolve eq1633 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3313 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) X3) = (M.op (M.op X1 (σ (M.op X4 X4))) (M.op (M.op X3 X2) (M.op X0 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1633 X4 (M.op (M.op X3 X2) (M.op X0 X2)) (M.op (M.op X1 X0) X3)
       have i₂ := eq54 X0 X3 X2 X1
       grind)
    | exact superpose eq54 eq1633
    | exact resolve eq1633 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1633
  have eq3314 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X3) = (M.op (M.op X1 (M.op X0 X2)) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3313 X0 X1 X2 X3 x
       have i₂ := eq2842 (M.op X3 X2) X1 (M.op X0 X2) x
       grind)
    | exact superpose eq2842 eq3313
    | exact resolve eq3313 eq2842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3313
  have eq11476 : ∀ X0 X1 : G, (τ X1) = (M.op (τ (M.op (M.op X1 X0) (M.op X0 X1))) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq239 X1 X0
       have i₂ := eq643 X1 (M.op X0 X1) X0
       grind)
    | (have i₁ := eq239 X1 X0
       have i₂ := eq643 X1 X0 (M.op X0 X1)
       grind)
    | exact superpose eq643 eq239
    | exact resolve eq239 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq643
  have eq18226 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op (M.op (σ X0) X1) X1))) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11476 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq2170 X0 X1
       grind)
    | exact superpose eq2170 eq11476
    | exact resolve eq11476 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170 eq11476
  have eq18335 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op (M.op (σ X0) X1) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18226 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18226
    | exact resolve eq18226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18226
  have eq18489 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op (σ X0) X1) (M.op (σ X0) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18335 X0 X1
       have i₂ := eq2842 (M.op (σ X0) X1) (σ X0) X1 X0
       grind)
    | exact superpose eq2842 eq18335
    | exact resolve eq18335 eq2842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2842 eq18335
  have eq22766 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1407 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq22767 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq22766 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22766
  have eq22803 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22767 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq22767
    | (have j0 := eq22767 (σ X0) (σ X1)
       grind)
    | exact resolve eq22767 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22807 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq22767 (τ X0) X1
       grind)
    | exact superpose eq22767 eq17
    | (have j1 := eq22767 (τ X0) X1
       grind)
    | exact resolve eq17 eq22767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq22767
  have eq24533 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op X0 (M.op X0 (τ (M.op (σ X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq566 (M.op (σ X0) X1) X0
       have i₂ := eq18489 X0 X1
       grind)
    | exact superpose eq18489 eq566
    | exact resolve eq566 eq18489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq18489
  have eq29206 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X3) X4) = (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X3 X4) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq280 X3 X4 (M.op X1 X2) X2
       have i₂ := eq981 X1 X2 X0
       grind)
    | (have i₁ := eq280 X3 X4 (M.op X1 X2) X2
       have i₂ := eq981 X1 X0 X2
       grind)
    | exact superpose eq981 eq280
    | exact resolve eq280 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq29225 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X3) X4) = (M.op X1 (M.op (M.op X3 X4) (M.op X0 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq280 X3 X4 (M.op (M.op X1 X2) X0) (M.op X0 X2)
       have i₂ := eq561 X1 X2 X0
       grind)
    | exact superpose eq561 eq280
    | exact resolve eq280 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq29318 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X5 (M.op X2 X1)) (M.op (M.op X0 X3) X1)) = (M.op (M.op X5 X4) (M.op (M.op (M.op X2 X0) X3) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq280 (M.op X2 X1) (M.op (M.op X0 X3) X1) X5 X4
       have i₂ := eq280 X0 X3 X2 X1
       grind)
    | exact superpose eq280 eq280
    | exact resolve eq280 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29851 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X5 (M.op X2 X1)) (M.op (M.op X0 X3) X1)) = (M.op (M.op X5 (M.op X2 X0)) X3) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq29318 X0 X1 X2 X3 x X5
       have i₂ := eq280 (M.op X2 X0) X3 X5 x
       grind)
    | exact superpose eq280 eq29318
    | exact resolve eq29318 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq29318
  have eq29939 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X3) X4) = (M.op X1 (M.op X3 (M.op X4 (M.op X0 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq29225 X0 X1 X2 X3 X4
       have i₂ := eq524 X3 X4 (M.op X0 X2) X1
       grind)
    | (have i₁ := eq29225 X1 X3 X2 X3 X4
       have i₂ := eq524 (M.op X3 X4) X1 X2 X3
       grind)
    | exact superpose eq524 eq29225
    | exact resolve eq29225 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29225
  have eq29957 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X3) X4) = (M.op (M.op (M.op X1 X0) X0) (M.op X3 (M.op X4 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq29206 X0 X1 X2 X3 X4
       have i₂ := eq524 X3 X4 X2 (M.op (M.op X1 X0) X0)
       grind)
    | (have i₁ := eq29206 X0 X1 (M.op X1 X2) X3 X4
       have i₂ := eq524 (M.op X3 X4) X1 X2 (M.op (M.op X1 X0) X0)
       grind)
    | exact superpose eq524 eq29206
    | exact resolve eq29206 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29206
  have eq30079 : ∀ X0 X2 X3 X5 : G, (M.op (M.op X5 (M.op X2 X0)) X3) = (M.op (M.op X5 X2) (M.op X0 X3)) := by
    intro X0 X2 X3 X5
    first
    | (have i₁ := eq29851 X0 x X2 X3 X5
       have i₂ := eq3314 X2 X5 x (M.op X0 X3)
       grind)
    | exact superpose eq3314 eq29851
    | exact resolve eq29851 eq3314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3314 eq29851
  have eq41053 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X3) X2) X4) = (M.op (M.op (M.op X1 X0) (M.op X2 X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq357 (M.op X0 X3) X2 X4 (M.op X1 X0)
       have i₂ := eq356 X0 X3 X2 X1
       grind)
    | exact superpose eq356 eq357
    | exact resolve eq357 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq357
  have eq41454 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X3) X2) X4) = (M.op (M.op (M.op X1 X0) X2) (M.op X4 (M.op X0 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq41053 X0 X1 X2 X3 X4
       have i₂ := eq30079 X4 X2 (M.op X0 X3) (M.op X1 X0)
       grind)
    | exact superpose eq30079 eq41053
    | exact resolve eq41053 eq30079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41053
  have eq114746 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X4 X0) X3) (M.op X1 X2)) = (M.op (M.op (M.op X4 X3) (M.op X0 X2)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1593 X1 X0 X2 (M.op X4 X3)
       have i₂ := eq1696 X0 X4 X3 (M.op X1 X2)
       grind)
    | (have i₁ := eq1593 X0 X3 X2 (M.op X1 X0)
       have i₂ := eq1696 X0 X1 (M.op X0 X2) X3
       grind)
    | exact superpose eq1696 eq1593
    | exact resolve eq1593 eq1696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593 eq1696
  have eq114896 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X4 X0) X3) (M.op X1 X2)) = (M.op (M.op (M.op X4 X3) X0) (M.op X2 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq114746 X0 X1 X2 X3 X4
       have i₂ := eq30079 X2 X0 X1 (M.op X4 X3)
       grind)
    | exact superpose eq30079 eq114746
    | exact resolve eq114746 eq30079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30079 eq114746
  have eq257182 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22807 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22807
    | exact resolve eq22807 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22807
  have eq257371 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq257182 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq257182
    | (have j0 := eq257182 X0 X1
       grind)
    | exact resolve eq257182 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257182
  have eq269201 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 X4) = (M.op (M.op (M.op (M.op X5 X3) X4) (τ (M.op (M.op (M.op X0 X1) X2) (M.op X0 (M.op X1 X2))))) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2737 X3 X5 X4 (M.op (M.op X0 X1) X2)
       have i₂ := eq524 X0 X1 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq524 eq2737
    | exact resolve eq2737 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524 eq2737
  have eq269791 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 X4) = (M.op X5 (M.op (τ (M.op (M.op (M.op X0 X1) X2) (M.op X0 (M.op X1 X2)))) (M.op X3 (M.op X4 X3)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq269201 X0 X1 X2 X3 X4 X5
       have i₂ := eq29939 X4 X5 X3 (τ (M.op (M.op (M.op X0 X1) X2) (M.op X0 (M.op X1 X2)))) X3
       grind)
    | exact superpose eq29939 eq269201
    | exact resolve eq269201 eq29939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29939 eq269201
  have eq270366 : ∀ X0 X1 X2 X4 X5 : G, (M.op X5 X4) = (M.op X5 (M.op (τ (M.op (M.op (M.op X0 X1) X2) (M.op X0 (M.op X1 X2)))) X4)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq269791 X0 X1 X2 x X4 X5
       have i₂ := eq292 X4 x (τ (M.op (M.op (M.op X0 X1) X2) (M.op X0 (M.op X1 X2))))
       grind)
    | exact superpose eq292 eq269791
    | exact resolve eq269791 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269791
  have eq270786 : ∀ X0 X2 X4 X5 : G, (M.op X5 X4) = (M.op X5 (M.op (τ (M.op (M.op (M.op X0 X2) X2) X0)) X4)) := by
    intro X0 X2 X4 X5
    first
    | (have i₁ := eq270366 X0 x X2 X4 X5
       have i₂ := eq41454 x X0 X2 X2 X0
       grind)
    | exact superpose eq41454 eq270366
    | exact resolve eq270366 eq41454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41454 eq270366
  have eq2563183 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22803 x y
       grind)
    | exact superpose eq22803 eq16
    | (have j1 := eq22803 x y
       grind)
    | exact resolve eq16 eq22803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22803
  have eq2566761 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2563183
       have i₂ := eq257371 x y
       grind)
    | exact superpose eq257371 eq2563183
    | (have j1 := eq257371 (σ x) (σ y)
       grind)
    | (have r₁ := eq2563183
       have r₂ := eq257371 x y
       grind)
    | exact resolve eq2563183 eq257371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257371 eq2563183
  have eq2566762 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2566761
  have eq2566778 : (τ (σ y)) = (M.op x (M.op x (τ (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24533 x (σ y)
       have i₂ := eq2566762
       grind)
    | exact superpose eq2566762 eq24533
    | exact resolve eq24533 eq2566762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24533
  have eq2566808 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) (M.op X0 (σ y)))) = (M.op X1 (M.op (σ x) X0)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq689 X0 (σ y) (σ x) X1
       have i₂ := eq2566762
       grind)
    | exact superpose eq2566762 eq689
    | exact resolve eq689 eq2566762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689 eq2566762
  have eq2567497 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (σ x) X0)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq2566808 X0 X1
       have i₂ := eq292 X0 (σ y) X1
       grind)
    | exact superpose eq292 eq2566808
    | exact resolve eq2566808 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292 eq2566808
  have eq2567506 : y = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2566778
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2566778
    | exact resolve eq2566778 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2566778
  have eq2568969 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X2) (M.op (M.op (σ x) X0) X0)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq949 X1 X2 (M.op (σ x) X0)
       have i₂ := eq2567497 X0 (M.op (σ x) X0)
       grind)
    | exact superpose eq2567497 eq949
    | exact resolve eq949 eq2567497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2567497
  have eq2570411 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X2) (M.op X0 (M.op (σ x) X0))) = X1 ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2568969 X0 X1 X2
       have i₂ := eq114896 X2 (M.op (σ x) X0) X0 X2 X1
       grind)
    | (have i₁ := eq2568969 X0 X1 X2
       have i₂ := eq114896 X2 X0 (M.op (σ x) X0) X2 X1
       grind)
    | exact superpose eq114896 eq2568969
    | exact resolve eq2568969 eq114896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114896 eq2568969
  have eq2571061 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) (σ x)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq2570411 X0 X1 x
       have i₂ := eq29957 x X1 X0 X0 (σ x)
       grind)
    | exact superpose eq29957 eq2570411
    | exact resolve eq2570411 eq29957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29957 eq2570411
  have eq2584884 : ∀ X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (τ (σ x)) X1)) ∨ y = (M.op x y) := by
    intro X1 X2
    first
    | (have i₁ := eq270786 (σ x) x X1 X2
       have i₂ := eq2571061 x (σ x)
       grind)
    | exact superpose eq2571061 eq270786
    | exact resolve eq270786 eq2571061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270786 eq2571061
  have eq2585288 : ∀ X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op x X1)) ∨ y = (M.op x y) := by
    intro X1 X2
    first
    | (have i₁ := eq2584884 X1 X2
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2584884
    | exact resolve eq2584884 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2584884
  have eq2597945 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2567506
       have i₂ := eq2585288 y x
       grind)
    | exact superpose eq2585288 eq2567506
    | exact resolve eq2567506 eq2585288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2567506 eq2585288
  have eq2597946 : y = (M.op x y) := by grind
  clear eq2597945
  have eq2597996 : ∀ X0 : G, x = (M.op (M.op y y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq949 x y X0
       have i₂ := eq2597946
       grind)
    | exact superpose eq2597946 eq949
    | exact resolve eq949 eq2597946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq2613699 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2385 y x
       have i₂ := eq2597996 x
       grind)
    | exact superpose eq2597996 eq2385
    | exact resolve eq2385 eq2597996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2385 eq2597996
  have eq2615833 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2613699
       grind)
    | exact superpose eq2613699 eq16
    | exact resolve eq16 eq2613699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2613699
  have eq2616310 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2615833
       have i₂ := eq2597946
       grind)
    | exact superpose eq2597946 eq2615833
    | exact resolve eq2615833 eq2597946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2597946 eq2615833
  have eq2616311 : False := by grind
  exact eq2616311

/-- `Equation2687`: `x = ((x ◇ y) ◇ (z ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_Equation2687 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2687 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2687.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq304 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq13 (σ X1) (σ X0)
       grind)
    | exact superpose eq13 eq15
    | (have j1 := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq304
    | (have j0 := eq304 X0 X1
       grind)
    | exact resolve eq304 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq317 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq311 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq311
    | (have j0 := eq311 X0 X1
       grind)
    | (have r₁ := eq311 X0 X0
       have r₂ := eq22 X0
       grind)
    | exact resolve eq311 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq673 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq673 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq673
    | (have j0 := eq673 X0 X1
       grind)
    | exact resolve eq673 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq714 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq700 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq700
    | (have j0 := eq700 X0 X1
       grind)
    | exact resolve eq700 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq1645 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq317 x y
       grind)
    | exact superpose eq317 eq16
    | (have j1 := eq317 x y
       grind)
    | exact resolve eq16 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq2283 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq714 x y
       grind)
    | exact superpose eq714 eq16
    | (have j1 := eq714 x y
       grind)
    | exact resolve eq16 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq15750 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) ≠ (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1645
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq1645
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq1645
       have r₂ := eq13 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1645
       have r₂ := eq13 (σ (k y x)) (σ (M.op x y))
       grind)
    | (have r₁ := eq1645
       have r₂ := eq13 (σ (M.op x x)) (σ (M.op y y))
       grind)
    | exact resolve eq1645 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq15751 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) ≠ (M.op y y) ∨ x = y := by grind
  clear eq15750
  have eq17306 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2283
       grind)
    | exact superpose eq2283 eq10
    | exact resolve eq10 eq2283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2283
  have eq17393 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17306
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq17306
    | exact resolve eq17306 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17306
  have eq17394 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq17393
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq17393
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq17393
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq17393
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq17393 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17393
  have eq17396 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17394
  have eq17397 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17396
  have eq30559 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15751
       have i₂ := eq17397
       grind)
    | exact superpose eq17397 eq15751
    | (have r₁ := eq15751
       have r₂ := eq17397
       grind)
    | exact resolve eq15751 eq17397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15751 eq17397
  have eq30563 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x x) ≠ (M.op x x) ∨ x = y := by grind
  clear eq30559
  have eq30564 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq30563
  have eq30567 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq30564
       grind)
    | exact superpose eq30564 eq10
    | exact resolve eq10 eq30564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30564
  have eq30667 : x = y ∨ x = y := by
    first
    | (have i₁ := eq30567
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30567
    | exact resolve eq30567 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30567
  have eq30668 : x = y := by grind
  clear eq30667
  have eq30670 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30668
       grind)
    | exact superpose eq30668 eq16
    | exact resolve eq16 eq30668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30668
  have eq30678 : False := by grind
  exact eq30678

/-- `Equation2688`: `x = ((x ◇ y) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyy_x_pxy_pxy_pyx_Equation2688 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2688 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2688.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op X0 (M.op X3 X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X2 X2)) X1 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X2 X2)) (M.op X1 X1) X2
       have i₂ := eq9 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq88 (σ X0)
       grind)
    | exact superpose eq88 eq15
    | exact resolve eq15 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq88 (τ X0)
       grind)
    | exact superpose eq88 eq19
    | exact resolve eq19 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq98 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq95
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq88 X0
       grind)
    | exact superpose eq88 eq91
    | exact resolve eq91 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq88 X0
       grind)
    | exact superpose eq88 eq98
    | exact resolve eq98 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq98
  have eq114 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (M.op X1 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq9
    | exact resolve eq9 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X2 (σ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq53
    | exact resolve eq53 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq131 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq124 X0 X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq124
    | (have j0 := eq124 X0 X1
       grind)
    | exact resolve eq124 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq144 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq162 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq144 (σ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq144
    | exact resolve eq144 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq169 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq162 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq162
    | exact resolve eq162 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq173 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq169 X0
       have i₂ := eq144 X0
       grind)
    | exact superpose eq144 eq169
    | exact resolve eq169 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq169
  have eq261 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2 x
       have i₂ := eq52 X0 X2 x X1
       grind)
    | (have i₁ := eq9 X0 (M.op x x) X2
       have i₂ := eq52 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq982 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq131 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq131 X0 X1
       grind)
    | exact superpose eq131 eq12
    | (have j1 := eq131 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq131 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq131 X0 X1
       grind)
    | exact resolve eq12 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq1011 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq982 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq1015 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1011 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1011
    | (have j0 := eq1011 X0 X1
       grind)
    | exact resolve eq1011 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1016 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1015 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq4004 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op X0 X0)) (M.op X2 X2)) (σ X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (σ (M.op X0 X0)) (σ X0) X1 X2
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq52
    | exact resolve eq52 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq173
  have eq4019 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) X0)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4004 X0 X1 x
       have i₂ := eq114 X0 x
       grind)
    | exact superpose eq114 eq4004
    | exact resolve eq4004 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq4004
  have eq4071 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X2 X2)) = (σ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4019 (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq261 X0 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq261 eq4019
    | exact resolve eq4019 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq4019
  have eq10354 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1016 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1016
    | exact resolve eq1016 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10384 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1016 x y
       grind)
    | exact superpose eq1016 eq16
    | (have j1 := eq1016 x y
       grind)
    | exact resolve eq16 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq10588 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10354 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10354
    | (have j0 := eq10354 X0 X1
       grind)
    | exact resolve eq10354 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10354
  have eq104164 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10588 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10588
    | (have j0 := eq10588 X1 (τ X0)
       grind)
    | exact resolve eq10588 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10588
  have eq104241 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq104164 X0 X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq104164
    | (have j0 := eq104164 X0 X1
       grind)
    | exact resolve eq104164 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq104164
  have eq151382 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10384
       have i₂ := eq104241 x y
       grind)
    | exact superpose eq104241 eq10384
    | (have j1 := eq104241 x y
       grind)
    | exact resolve eq10384 eq104241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10384 eq104241
  have eq151385 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq151382
  have eq151443 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq151385
       grind)
    | exact superpose eq151385 eq10
    | exact resolve eq10 eq151385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151385
  have eq151512 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq151443
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq151443
    | exact resolve eq151443 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151443
  have eq151513 : y = (M.op x x) := by grind
  clear eq151512
  have eq151518 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 x
       have i₂ := eq151513
       grind)
    | exact superpose eq151513 eq53
    | exact resolve eq53 eq151513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq151535 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq115 x X0 X1
       have i₂ := eq151513
       grind)
    | exact superpose eq151513 eq115
    | exact resolve eq115 eq151513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq151513
  have eq155052 : ∀ X0 X2 : G, (σ (M.op X0 (M.op X2 X2))) = (M.op (σ X0) y) := by
    intro X0 X2
    first
    | (have i₁ := eq4071 X0 X2 x
       have i₂ := eq151518 (σ X0) x
       grind)
    | exact superpose eq151518 eq4071
    | exact resolve eq4071 eq151518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4071
  have eq155142 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq155052 X0 x
       have i₂ := eq151518 X0 x
       grind)
    | exact superpose eq151518 eq155052
    | exact resolve eq155052 eq151518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155052
  have eq168331 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq151535 X0 x
       have i₂ := eq151518 X0 x
       grind)
    | exact superpose eq151518 eq151535
    | exact resolve eq151535 eq151518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151518 eq151535
  have eq169013 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq168331 (σ x)
       grind)
    | exact superpose eq168331 eq16
    | exact resolve eq16 eq168331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168331
  have eq169099 : False := by grind
  exact eq169099

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq26 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) = (k (M.op (M.op X1 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) = (k (M.op (M.op X1 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq69 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq61
    | exact resolve eq61 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq77 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq69 X0
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq9
    | exact resolve eq9 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq9
    | exact resolve eq9 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq77 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq94 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq78
    | exact resolve eq78 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq12 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq112 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq131 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq80 X0
       have i₂ := eq94 X0 X0
       grind)
    | exact superpose eq94 eq80
    | exact resolve eq80 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq133 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq131 (σ X0)
       grind)
    | exact superpose eq131 eq22
    | exact resolve eq22 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq142 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) X1))) = (σ (M.op (M.op (τ X0) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) X1)
       have i₂ := eq118 (τ X0) X1
       grind)
    | exact superpose eq118 eq17
    | exact resolve eq17 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq511 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq75
    | exact resolve eq75 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1336 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq142 X0 (M.op (M.op (τ X0) (τ X0)) X1)
       have i₂ := eq79 (τ X0) X1
       grind)
    | exact superpose eq79 eq142
    | exact resolve eq142 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1341 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq142 X0 (τ X0)
       have i₂ := eq69 (τ X0)
       grind)
    | exact superpose eq69 eq142
    | exact resolve eq142 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq142
  have eq1355 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1341 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1341
    | exact resolve eq1341 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq1360 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1336 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1336
    | exact resolve eq1336 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq1637 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1653 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1637 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1637
    | (have j0 := eq1637 X0 (σ X1)
       grind)
    | exact resolve eq1637 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1658 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op X0 (τ (M.op (σ X0) (σ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1637 (τ (M.op (σ X0) (σ X0))) X0
       have i₂ := eq133 X0
       grind)
    | exact superpose eq133 eq1637
    | (have j0 := eq1637 X0 X0
       grind)
    | exact resolve eq1637 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq1691 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1637 (τ X1) X0
       grind)
    | exact superpose eq1637 eq17
    | (have j1 := eq1637 X0 X0
       grind)
    | exact resolve eq17 eq1637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq1718 : ∀ X0 : G, (k X0 (k X0 (σ (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1355 X0
       have i₂ := eq1691 (τ X0) X0
       grind)
    | exact superpose eq1691 eq1355
    | (have j1 := eq1691 (τ X0) x
       grind)
    | exact resolve eq1355 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355 eq1691
  have eq1739 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1718 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1718
    | (have j0 := eq1718 X0
       grind)
    | exact resolve eq1718 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq1859 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) (M.op (τ X0) X1)))) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1360 X0 X1
       have i₂ := eq1739 X0
       grind)
    | exact superpose eq1739 eq1360
    | (have j1 := eq1739 X0
       grind)
    | exact resolve eq1360 eq1739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360
  have eq1871 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ X0)) X1) = X1 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78 (τ X0) X1
       have i₂ := eq1739 X0
       grind)
    | exact superpose eq1739 eq78
    | (have j1 := eq1739 X0
       grind)
    | exact resolve eq78 eq1739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1891 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) (M.op (τ X0) X1)) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq511 (τ X0) (τ X0) x
       have i₂ := eq1739 X0
       grind)
    | exact superpose eq1739 eq511
    | (have j1 := eq1739 X0
       grind)
    | exact resolve eq511 eq1739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739
  have eq1896 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) X1) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1891 X0 X1
       have i₂ := eq94 (τ X0) X1
       grind)
    | exact superpose eq94 eq1891
    | (have j0 := eq1891 X0 X1
       grind)
    | exact resolve eq1891 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891
  have eq1911 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) X1))) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1859 X0 X1
       have i₂ := eq94 (τ X0) X1
       grind)
    | exact superpose eq94 eq1859
    | (have j0 := eq1859 X0 X1
       grind)
    | exact resolve eq1859 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859
  have eq1989 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1653 X1 X0
       have i₂ := eq1637 X1 X0
       grind)
    | exact superpose eq1637 eq1653
    | (have j0 := eq1653 X0 X0
       have j1 := eq1637 X0 (σ X0)
       grind)
    | exact resolve eq1653 eq1637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653
  have eq4758 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1896 eq1871
    | (have j0 := eq1871 X0 X1
       have j1 := eq1896 X0 X1
       grind)
    | exact resolve eq1871 eq1896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871 eq1896
  have eq4760 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq4758 eq1911
    | (have j0 := eq1911 X0 X1
       have j1 := eq4758 X0 X1
       grind)
    | exact resolve eq1911 eq4758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911 eq4758
  have eq4918 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (τ X0) = (k (τ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (τ X0) X0 (τ X0)
       have i₂ := eq4760 (τ X0) X1
       grind)
    | exact superpose eq4760 eq26
    | (have j1 := eq4760 (τ X0) X1
       grind)
    | exact resolve eq26 eq4760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4760
  have eq4941 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (σ X1)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4918 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4918
    | (have j0 := eq4918 X0 X1
       grind)
    | exact resolve eq4918 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4918
  have eq5085 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op X1 (τ X0)) (M.op X1 X2))) X0) = (σ (M.op (τ X0) (M.op (M.op X1 (τ X0)) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op (M.op X1 (τ X0)) (M.op X1 X2))
       have i₂ := eq64 (τ X0) X1 X2
       grind)
    | exact superpose eq64 eq18
    | exact resolve eq18 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq64
  have eq5666 : ∀ X0 X1 : G, (k X1 (k X1 X1)) = X1 ∨ (τ X1) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4941 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4941
    | (have j0 := eq4941 X1 X1
       grind)
    | exact resolve eq4941 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4941
  have eq5704 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (k (σ X0) (σ X0)))) ∨ (τ (σ X0)) = (k (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (k (σ X0) (σ X0))
       have i₂ := eq5666 X1 (σ X0)
       grind)
    | exact superpose eq5666 eq28
    | (have j1 := eq5666 X1 (σ X0)
       grind)
    | exact resolve eq28 eq5666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5666
  have eq5723 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (k (τ (σ X0)) X0)) ∨ (τ (σ X0)) = (k (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5704 X0 X1
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq5704
    | (have j0 := eq5704 X0 X1
       grind)
    | exact resolve eq5704 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5704
  have eq5738 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (τ (σ X0)) = (k (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5723 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5723
    | (have j0 := eq5723 X0 X1
       grind)
    | exact resolve eq5723 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5723
  have eq5744 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5738 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5738
    | (have j0 := eq5738 X0 X1
       grind)
    | exact resolve eq5738 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5738
  have eq5765 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq5744 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5744
  have eq5766 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq5765 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5765
  have eq5800 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5766 X0
       have i₂ := eq1637 X0 (k X0 X0)
       grind)
    | exact superpose eq1637 eq5766
    | (have j1 := eq1637 X0 (k X0 X0)
       grind)
    | exact resolve eq5766 eq1637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637 eq5766
  have eq5980 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 X0) X1) (k X0 X0)) X1) = X1 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78 (k X0 X0) X1
       have i₂ := eq5800 X0
       grind)
    | exact superpose eq5800 eq78
    | (have j1 := eq5800 X0
       grind)
    | exact resolve eq78 eq5800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6015 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (k X0 X0) (M.op (k X0 X0) X1)) (k X0 X0)) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq511 (k X0 X0) (k X0 X0) x
       have i₂ := eq5800 X0
       grind)
    | exact superpose eq5800 eq511
    | (have j1 := eq5800 X0
       grind)
    | exact resolve eq511 eq5800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5800
  have eq6022 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) (k X0 X0)) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6015 X0 X1
       have i₂ := eq94 (k X0 X0) X1
       grind)
    | exact superpose eq94 eq6015
    | (have j0 := eq6015 X0 X1
       grind)
    | exact resolve eq6015 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6015
  have eq21977 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1658 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1658
    | (have j0 := eq1658 (τ X0)
       grind)
    | exact resolve eq1658 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1658
  have eq36045 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = X1 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq6022 eq5980
    | (have j0 := eq5980 X0 X1
       have j1 := eq6022 X0 X1
       grind)
    | exact resolve eq5980 eq6022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5980 eq6022
  have eq36357 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq36045 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36045
  have eq36358 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq36357 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36357
  have eq36493 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq36358 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36358
  have eq36645 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (k X0 X0) X0
       have i₂ := eq36493 X0
       grind)
    | exact superpose eq36493 eq9
    | exact resolve eq9 eq36493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36493
  have eq37397 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1989 x y
       grind)
    | exact superpose eq1989 eq16
    | (have j1 := eq1989 x x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1989 x y
       grind)
    | exact resolve eq16 eq1989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989
  have eq37533 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq37397
  have eq39461 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21977 (σ x)
       have i₂ := eq37533
       grind)
    | exact superpose eq37533 eq21977
    | (have j0 := eq21977 (σ x)
       grind)
    | exact resolve eq21977 eq37533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21977 eq37533
  have eq39536 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by grind
  clear eq39461
  have eq39577 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39536
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq39536
    | exact resolve eq39536 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39536
  have eq39578 : x = (M.op x x) := by grind
  clear eq39577
  have eq39614 : x = (M.op x x) := by grind
  clear eq39578
  have eq39652 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq78 x X0
       have i₂ := eq39614
       grind)
    | exact superpose eq39614 eq78
    | exact resolve eq78 eq39614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq39729 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq511 x x x
       have i₂ := eq39614
       grind)
    | exact superpose eq39614 eq511
    | exact resolve eq511 eq39614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39614
  have eq39765 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq39729 X0
       have i₂ := eq94 x X0
       grind)
    | exact superpose eq94 eq39729
    | exact resolve eq39729 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq39729
  have eq41173 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39652 X0
       have i₂ := eq39765 X0
       grind)
    | exact superpose eq39765 eq39652
    | exact resolve eq39652 eq39765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39652
  have eq41174 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41173 y
       grind)
    | exact superpose eq41173 eq16
    | exact resolve eq16 eq41173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41175 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq39765 X0
       have i₂ := eq41173 X0
       grind)
    | exact superpose eq41173 eq39765
    | exact resolve eq39765 eq41173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39765
  have eq41258 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq511 x X1 X0
       have i₂ := eq41173 X0
       grind)
    | exact superpose eq41173 eq511
    | exact resolve eq511 eq41173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq41409 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41258 X0 X0
       have i₂ := eq41173 X0
       grind)
    | exact superpose eq41173 eq41258
    | exact resolve eq41258 eq41173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41173 eq41258
  have eq42807 : ∀ X0 X1 : G, (k (σ (M.op (M.op X0 (τ X1)) x)) X1) = (σ (M.op (τ X1) (M.op (M.op X0 (τ X1)) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq5085 X0 X0 x
       have i₂ := eq41175 X0
       grind)
    | exact superpose eq41175 eq5085
    | exact resolve eq5085 eq41175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5085
  have eq43016 : ∀ X1 : G, (k (σ x) X1) = (σ (M.op (τ X1) x)) := by
    intro X1
    first
    | (have i₁ := eq42807 x X1
       have i₂ := eq41175 (M.op x (τ X1))
       grind)
    | exact superpose eq41175 eq42807
    | exact resolve eq42807 eq41175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42807
  have eq43082 : ∀ X1 : G, (σ x) = (k (σ x) X1) := by
    intro X1
    first
    | (have i₁ := eq43016 X1
       have i₂ := eq41175 (τ X1)
       grind)
    | exact superpose eq41175 eq43016
    | exact resolve eq43016 eq41175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41175 eq43016
  have eq43682 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq36645 (σ x) X0
       have i₂ := eq43082 (σ x)
       grind)
    | exact superpose eq43082 eq36645
    | exact resolve eq36645 eq43082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36645 eq43082
  have eq43776 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq43682 X0
       have i₂ := eq41409 X0 (σ x)
       grind)
    | exact superpose eq41409 eq43682
    | exact resolve eq43682 eq41409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41409 eq43682
  have eq43894 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq41174
       have i₂ := eq43776 (σ y)
       grind)
    | exact superpose eq43776 eq41174
    | (have r₁ := eq41174
       have r₂ := eq43776 (σ y)
       grind)
    | exact resolve eq41174 eq43776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41174 eq43776
  have eq44037 : False := by grind
  exact eq44037
