import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then X else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_x_pxx_Equation1027 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) Law1027 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq62 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x X0)) X2
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 (M.op X0 x)
       have i₂ := eq62 X0 x
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq82 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq65 X0
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq83 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq83 (σ X1) (σ X0)
       grind)
    | exact superpose eq83 eq15
    | exact resolve eq15 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq83 X1 X0
       grind)
    | exact superpose eq83 eq86
    | exact resolve eq86 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq86
  have eq265 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq16
    | (have r₁ := eq16
       have r₂ := eq97 x y
       grind)
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq273 : False := by grind
  exact eq273

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then X else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_x_pyy_Equation1027 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq62 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x X0)) X2
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 (M.op X0 x)
       have i₂ := eq62 X0 x
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq82 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq65 X0
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq83 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq83 (σ X1) (σ X0)
       grind)
    | exact superpose eq83 eq15
    | exact resolve eq15 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq83 X1 X0
       grind)
    | exact superpose eq83 eq86
    | exact resolve eq86 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq86
  have eq265 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq16
    | (have r₁ := eq16
       have r₂ := eq97 x y
       grind)
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq273 : False := by grind
  exact eq273

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x X0)) X2
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq109 X0 (M.op X0 x)
       have i₂ := eq109 X0 x
       grind)
    | exact superpose eq109 eq109
    | exact resolve eq109 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq167 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq168 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3345 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq167 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq16672 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = X1 ∨ (σ X0) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq168 X0 X1
       grind)
    | exact superpose eq168 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq168 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq168 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq168 X0 (M.op (σ X0) X1)
       grind)
    | exact resolve eq13 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq16695 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = X1 ∨ (σ X0) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq16672 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16672
  have eq16696 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq16695 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16695
  have eq16986 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16696 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16696
    | exact resolve eq16696 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16696
  have eq17153 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16986 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq16986
    | (have j0 := eq16986 X0 X1
       grind)
    | exact resolve eq16986 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq16986
  have eq17230 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq17153 X0 (σ X1)
       grind)
    | exact superpose eq17153 eq28
    | (have j1 := eq17153 X0 (σ X1)
       grind)
    | exact resolve eq28 eq17153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq17239 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq17153 X0 X1
       grind)
    | exact superpose eq17153 eq11
    | (have j1 := eq17153 X0 X1
       grind)
    | exact resolve eq11 eq17153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17153
  have eq17383 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17239 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq17239
    | (have j0 := eq17239 X0 X1
       grind)
    | exact resolve eq17239 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17239
  have eq17489 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq17383 X0 (τ X1)
       grind)
    | exact superpose eq17383 eq19
    | (have j1 := eq17383 X0 (τ X1)
       grind)
    | exact resolve eq19 eq17383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq17383
  have eq18024 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq17230 (σ X0) X1
       grind)
    | exact superpose eq17230 eq37
    | (have j1 := eq17230 (σ X0) X1
       grind)
    | exact resolve eq37 eq17230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq17230
  have eq18096 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18024 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq18024
    | (have j0 := eq18024 X0 X1
       grind)
    | exact resolve eq18024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18024
  have eq18133 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18096 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18096
    | (have j0 := eq18096 X0 X1
       grind)
    | exact resolve eq18096 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18096
  have eq18147 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18133 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18133
    | (have j0 := eq18133 X0 X1
       grind)
    | exact resolve eq18133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18133
  have eq18163 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17489 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17489
    | exact resolve eq17489 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17489
  have eq18284 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18163 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq18163
    | (have j0 := eq18163 X0 X1
       grind)
    | exact resolve eq18163 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18163
  have eq18599 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq18147 X0 X1
       grind)
    | exact superpose eq18147 eq11
    | (have j1 := eq18147 X0 X1
       grind)
    | exact resolve eq11 eq18147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18147
  have eq20349 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18599 x y
       grind)
    | exact superpose eq18599 eq16
    | (have j1 := eq18599 x y
       grind)
    | exact resolve eq16 eq18599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18599
  have eq20587 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq20349
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq20349
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq20349
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq20349
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq20349 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20588 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq20349
       have i₂ := eq18284 y x
       grind)
    | exact superpose eq18284 eq20349
    | (have j1 := eq18284 y x
       grind)
    | (have r₁ := eq20349
       have r₂ := eq18284 y x
       grind)
    | (have r₁ := eq20349
       have r₂ := eq18284 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq20349
       have r₂ := eq18284 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq20349 eq18284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18284 eq20349
  have eq20593 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20588
  have eq20594 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq20593
  have eq20595 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20587
  have eq20596 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq20595
  have eq20601 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20594
       grind)
    | exact superpose eq20594 eq16
    | exact resolve eq16 eq20594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20594
  have eq20602 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq20601
       have r₂ := eq22 x
       grind)
    | exact resolve eq20601 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20601
  have eq20611 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3345 x y
       have i₂ := eq20602
       grind)
    | exact superpose eq20602 eq3345
    | (have j0 := eq3345 x y
       grind)
    | exact resolve eq3345 eq20602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3345 eq20602
  have eq20616 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq20611
  have eq20617 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20616
  have eq20622 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20596
       grind)
    | exact superpose eq20596 eq16
    | exact resolve eq16 eq20596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20596
  have eq20626 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20622
       have r₂ := eq22 x
       grind)
    | exact resolve eq20622 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20622
  have eq20629 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20626
       grind)
    | exact superpose eq20626 eq10
    | exact resolve eq10 eq20626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20626
  have eq20699 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20629
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20629
    | exact resolve eq20629 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20629
  have eq20706 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20699
       grind)
    | exact superpose eq20699 eq16
    | exact resolve eq16 eq20699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20699
  have eq20710 : x = (M.op x y) := by
    first
    | (have r₁ := eq20706
       have r₂ := eq22 x
       grind)
    | exact resolve eq20706 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20706
  have eq21248 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20617
       grind)
    | exact superpose eq20617 eq16
    | exact resolve eq16 eq20617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20617
  have eq21320 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21248
       have i₂ := eq114 (σ x)
       grind)
    | exact superpose eq114 eq21248
    | exact resolve eq21248 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq21248
  have eq21327 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21320
       have i₂ := eq20710
       grind)
    | exact superpose eq20710 eq21320
    | exact resolve eq21320 eq20710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21320
  have eq21328 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21327
  have eq21345 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21328
       grind)
    | exact superpose eq21328 eq16
    | exact resolve eq16 eq21328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21328
  have eq21381 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq21345
       have i₂ := eq20710
       grind)
    | exact superpose eq20710 eq21345
    | exact resolve eq21345 eq20710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20710 eq21345
  have eq21382 : False := by grind
  exact eq21382

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyy_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x X0)) X2
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq109 X0 (M.op X0 x)
       have i₂ := eq109 X0 x
       grind)
    | exact superpose eq109 eq109
    | exact resolve eq109 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq149 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq823 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 (M.op (τ X0) x)
       have i₂ := eq109 (τ X0) x
       grind)
    | exact superpose eq109 eq150
    | (have j0 := eq150 X0 (M.op (τ X0) X1)
       grind)
    | exact resolve eq150 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq150 X1 X0
       grind)
    | exact superpose eq150 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq150 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq150 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X0)
       have r₂ := eq150 X0 (M.op X0 (τ X0))
       grind)
    | exact resolve eq13 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq109 (τ X1) X0
       have i₂ := eq150 X1 X0
       grind)
    | exact superpose eq150 eq109
    | (have j1 := eq150 X1 X0
       grind)
    | exact resolve eq109 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq840 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq828 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq841 : ∀ X0 X1 : G, (τ X1) = X0 ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq840 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq844 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq823 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq851 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq841 X0 X1
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq841
    | (have j0 := eq841 X0 X1
       grind)
    | exact resolve eq841 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq855 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k X0 (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq844 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq844
    | (have j0 := eq844 X0 X1
       grind)
    | exact resolve eq844 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq881 : ∀ X0 X1 : G, (τ X1) = X0 ∨ (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq855 X0 X1
       have i₂ := eq150 X0 X1
       grind)
    | exact superpose eq150 eq855
    | (have j1 := eq150 X1 X0
       grind)
    | exact resolve eq855 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq896 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k X1 (σ X0)) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq881 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq917 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq148 x y
       grind)
    | exact superpose eq148 eq16
    | (have j1 := eq148 x y
       grind)
    | exact resolve eq16 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq5936 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq851 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq851
    | exact resolve eq851 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq6004 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5936 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5936
    | (have j0 := eq5936 X0 X1
       grind)
    | exact resolve eq5936 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5936
  have eq6077 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq6004 X0 X1
       grind)
    | exact superpose eq6004 eq10
    | (have j1 := eq6004 X0 X1
       grind)
    | exact resolve eq10 eq6004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6004
  have eq6136 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6077 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq6077
    | (have j0 := eq6077 X0 X1
       grind)
    | exact resolve eq6077 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6077
  have eq6229 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq6136 (σ X0) X1
       grind)
    | exact superpose eq6136 eq37
    | (have j1 := eq6136 (σ X0) X1
       grind)
    | exact resolve eq37 eq6136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6136
  have eq9423 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq896 X1 X0
       grind)
    | exact superpose eq896 eq10
    | (have j1 := eq896 X1 X0
       grind)
    | exact resolve eq10 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq9465 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9423 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq9423
    | (have j0 := eq9423 X0 X1
       grind)
    | exact resolve eq9423 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq9423
  have eq9558 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq9465 (σ X0) X1
       grind)
    | exact superpose eq9465 eq15
    | (have j1 := eq9465 (σ X0) X1
       grind)
    | exact resolve eq15 eq9465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9561 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq9465 (σ X0) X1
       grind)
    | exact superpose eq9465 eq37
    | (have j1 := eq9465 (σ X0) X1
       grind)
    | exact resolve eq37 eq9465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9465
  have eq9622 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9561 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq9561
    | (have j0 := eq9561 X0 X1
       grind)
    | exact resolve eq9561 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9561
  have eq9625 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9558 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9558
    | (have j0 := eq9558 X0 X1
       grind)
    | exact resolve eq9558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9558
  have eq9658 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9622 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9622
    | (have j0 := eq9622 X0 X1
       grind)
    | exact resolve eq9622 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9622
  have eq9661 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9625 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9625
    | (have j0 := eq9625 X0 X1
       grind)
    | exact resolve eq9625 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9625
  have eq9675 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9658 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9658
    | (have j0 := eq9658 X0 X1
       grind)
    | exact resolve eq9658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9658
  have eq9686 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9675 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9675
    | (have j0 := eq9675 X0 X1
       grind)
    | exact resolve eq9675 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9675
  have eq9752 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq9686 X0 (τ X1)
       grind)
    | exact superpose eq9686 eq19
    | (have j1 := eq9686 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq9686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9848 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq9686 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9686
  have eq17330 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6229 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6229
    | exact resolve eq6229 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6229
  have eq17488 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17330 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq17330
    | (have j0 := eq17330 X0 X1
       grind)
    | exact resolve eq17330 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq17330
  have eq20774 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9752 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9752
    | exact resolve eq9752 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9752
  have eq20888 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20774 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq20774
    | (have j0 := eq20774 X0 X1
       grind)
    | exact resolve eq20774 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20774
  have eq47688 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq830 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq830
    | exact resolve eq830 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq47893 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47688 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq47688
    | (have j0 := eq47688 X0 X1
       grind)
    | exact resolve eq47688 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47688
  have eq48033 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq47893 X0 (τ X1)
       grind)
    | exact superpose eq47893 eq19
    | (have j1 := eq47893 X0 (τ X1)
       grind)
    | exact resolve eq19 eq47893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq48058 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq47893 X0 X1
       grind)
    | exact superpose eq47893 eq10
    | (have j1 := eq47893 X0 X1
       grind)
    | exact resolve eq10 eq47893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47893
  have eq48210 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48058 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq48058
    | (have j0 := eq48058 X0 X1
       grind)
    | exact resolve eq48058 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48058
  have eq48295 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ X0) = X1 ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 X1
       have i₂ := eq48210 (σ X0) X1
       grind)
    | exact superpose eq48210 eq149
    | (have j0 := eq149 X0 X1
       have j1 := eq48210 (σ X0) X1
       grind)
    | exact resolve eq149 eq48210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq48353 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq48295 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48295
  have eq48403 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48353 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48353
    | (have j0 := eq48353 X0 X1
       grind)
    | exact resolve eq48353 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48353
  have eq48916 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (σ X0) = (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq48403 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48403
    | (have j0 := eq48403 X0 (σ X1)
       grind)
    | exact resolve eq48403 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48403
  have eq49126 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48916 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq48916
    | (have j0 := eq48916 X0 X1
       grind)
    | exact resolve eq48916 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48916
  have eq49731 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (τ X0) = (τ X1) ∨ (τ X0) = (τ X1) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48033 (τ X0) X1
       have i₂ := eq150 X0 (τ X1)
       grind)
    | exact superpose eq150 eq48033
    | (have j0 := eq48033 (τ X1) X0
       have j1 := eq150 X1 (τ X0)
       grind)
    | exact resolve eq48033 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq48033
  have eq49870 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (τ X0) = (τ X1) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq49731 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49731
  have eq49898 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (τ X0) = (τ X1) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq49870 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq49870
    | (have j0 := eq49870 X0 X1
       grind)
    | exact resolve eq49870 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49870
  have eq49910 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ X0) = (τ X1) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq49898 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49898
    | (have j0 := eq49898 X0 X1
       grind)
    | exact resolve eq49898 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49898
  have eq49916 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49910 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49910
    | (have j0 := eq49910 X0 X1
       grind)
    | exact resolve eq49910 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49910
  have eq50834 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49916 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49916
    | (have j0 := eq49916 X1 (σ X0)
       grind)
    | exact resolve eq49916 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49916
  have eq51334 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49126 y x
       grind)
    | exact superpose eq49126 eq16
    | (have j1 := eq49126 y x
       grind)
    | exact resolve eq16 eq49126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49126
  have eq51690 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq51334
       have i₂ := eq20888 y x
       grind)
    | exact superpose eq20888 eq51334
    | (have j1 := eq20888 x (k x y)
       grind)
    | (have r₁ := eq51334
       have r₂ := eq20888 y x
       grind)
    | (have r₁ := eq51334
       have r₂ := eq20888 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq51334
       have r₂ := eq20888 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq51334 eq20888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20888 eq51334
  have eq51695 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq51690
  have eq51696 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq51695
  have eq51705 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51696
       grind)
    | exact superpose eq51696 eq16
    | exact resolve eq16 eq51696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51696
  have eq51709 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq51705
       have r₂ := eq22 x
       grind)
    | exact resolve eq51705 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51705
  have eq51723 : (τ x) = (τ (M.op x y)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17488 x y
       have i₂ := eq51709
       grind)
    | exact superpose eq51709 eq17488
    | (have j0 := eq17488 (τ x) (τ (M.op x y))
       grind)
    | exact resolve eq17488 eq51709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17488 eq51709
  have eq51750 : x = y ∨ (τ x) = (τ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq51723
  have eq53065 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (τ x) = (τ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51750
       grind)
    | exact superpose eq51750 eq16
    | exact resolve eq16 eq51750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51750
  have eq53082 : (σ x) = (σ y) ∨ (τ x) = (τ (M.op x y)) := by
    first
    | (have r₁ := eq53065
       have r₂ := eq22 x
       grind)
    | exact resolve eq53065 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53065
  have eq53088 : y = (τ (σ x)) ∨ (τ x) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq53082
       grind)
    | exact superpose eq53082 eq10
    | exact resolve eq10 eq53082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53082
  have eq53203 : x = y ∨ (τ x) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq53088
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq53088
    | exact resolve eq53088 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53088
  have eq53210 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (τ x) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53203
       grind)
    | exact superpose eq53203 eq16
    | exact resolve eq16 eq53203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53203
  have eq53227 : (τ x) = (τ (M.op x y)) := by
    first
    | (have r₁ := eq53210
       have r₂ := eq22 x
       grind)
    | exact resolve eq53210 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53210
  have eq53241 : (M.op x y) = (σ (τ x)) := by
    first
    | (have i₁ := eq11 (M.op x y)
       have i₂ := eq53227
       grind)
    | exact superpose eq53227 eq11
    | exact resolve eq11 eq53227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53227
  have eq53420 : x = (M.op x y) := by
    first
    | (have i₁ := eq53241
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq53241
    | exact resolve eq53241 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53241
  have eq53459 : x ≠ x ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq9848 x y
       have i₂ := eq53420
       grind)
    | exact superpose eq53420 eq9848
    | (have j0 := eq9848 x y
       grind)
    | (have r₁ := eq9848 x y
       have r₂ := eq53420
       grind)
    | exact resolve eq9848 eq53420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9848
  have eq53479 : x = y ∨ x = (k x y) := by grind
  clear eq53459
  have eq53550 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53479
       grind)
    | exact superpose eq53479 eq16
    | exact resolve eq16 eq53479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53479
  have eq53571 : x = (k x y) := by
    first
    | (have r₁ := eq53550
       have r₂ := eq22 x
       grind)
    | exact resolve eq53550 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53550
  have eq64237 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (k (σ X0) X1) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 (τ X1))
       have i₂ := eq50834 X0 X1
       grind)
    | exact superpose eq50834 eq10
    | (have j1 := eq50834 X0 X1
       grind)
    | exact resolve eq10 eq50834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50834
  have eq64380 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (k (σ X0) X1) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64237 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq64237
    | (have j0 := eq64237 X0 X1
       grind)
    | exact resolve eq64237 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq64237
  have eq64504 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64380 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq64380
    | (have j0 := eq64380 X1 (σ X0)
       grind)
    | exact resolve eq64380 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64380
  have eq64824 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64504 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq64504
    | (have j0 := eq64504 X0 X1
       grind)
    | exact resolve eq64504 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64504
  have eq65018 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9661 X1 X0
       have i₂ := eq64824 X0 X1
       grind)
    | exact superpose eq64824 eq9661
    | (have j0 := eq9661 X1 X0
       have j1 := eq64824 X0 X1
       grind)
    | exact resolve eq9661 eq64824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9661 eq64824
  have eq65192 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq65018 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65018
  have eq65722 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq917
       have i₂ := eq65192 y x
       grind)
    | exact superpose eq65192 eq917
    | (have j1 := eq65192 x y
       grind)
    | (have r₁ := eq917
       have r₂ := eq65192 (M.op x y) (k x y)
       grind)
    | (have r₁ := eq917
       have r₂ := eq65192 (k x y) (M.op x y)
       grind)
    | (have r₁ := eq917
       have r₂ := eq65192 (σ (M.op x y)) (σ (k x y))
       grind)
    | exact resolve eq917 eq65192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq65192
  have eq65750 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq65722
  have eq65751 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq65750
  have eq66094 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65751
       grind)
    | exact superpose eq65751 eq16
    | exact resolve eq16 eq65751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65751
  have eq66157 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq66094
       have r₂ := eq22 x
       grind)
    | exact resolve eq66094 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq66094
  have eq66172 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66157
       grind)
    | exact superpose eq66157 eq16
    | exact resolve eq16 eq66157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66157
  have eq66313 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66172
       have i₂ := eq114 (σ x)
       grind)
    | exact superpose eq114 eq66172
    | exact resolve eq66172 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq66172
  have eq66326 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66313
       have i₂ := eq53420
       grind)
    | exact superpose eq53420 eq66313
    | exact resolve eq66313 eq53420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66313
  have eq66327 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq66326
  have eq66384 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66327
       grind)
    | exact superpose eq66327 eq16
    | exact resolve eq16 eq66327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66470 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48210 (σ x) (σ y)
       have i₂ := eq66327
       grind)
    | exact superpose eq66327 eq48210
    | (have j0 := eq48210 (σ x) (σ y)
       grind)
    | exact resolve eq48210 eq66327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48210 eq66327
  have eq66472 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq66470
  have eq66494 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq66472
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq66472
    | exact resolve eq66472 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66472
  have eq66564 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq66384
       have i₂ := eq53420
       grind)
    | exact superpose eq53420 eq66384
    | exact resolve eq66384 eq53420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53420 eq66384
  have eq66576 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq66494
       have i₂ := eq53571
       grind)
    | exact superpose eq53571 eq66494
    | exact resolve eq66494 eq53571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53571 eq66494
  have eq66577 : (σ x) = (σ y) := by grind
  clear eq66576
  have eq66612 : False := by grind
  exact eq66612

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_x_pyx_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq75 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x X0)) X2
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq75 X0 (M.op X0 x)
       have i₂ := eq75 X0 x
       grind)
    | exact superpose eq75 eq75
    | exact resolve eq75 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq380 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101
    | exact resolve eq101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq411 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq380
    | (have j0 := eq380 X0 X1
       grind)
    | exact resolve eq380 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq419 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X1 X0
       have i₂ := eq411 X1 X0
       grind)
    | exact superpose eq411 eq75
    | (have j1 := eq411 X1 X0
       grind)
    | exact resolve eq75 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq451 : ∀ X0 X1 : G, X0 = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq411 X0 X1
       have i₂ := eq419 X1 X0
       grind)
    | exact superpose eq419 eq411
    | (have j0 := eq411 X0 X1
       have j1 := eq419 X1 X0
       grind)
    | exact resolve eq411 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq419
  have eq460 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq451 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq477 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq460 X1 X0
       grind)
    | exact superpose eq460 eq10
    | (have j1 := eq460 (k X0 X1) (τ (σ (M.op X0 X1)))
       grind)
    | exact resolve eq10 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq477 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq477
    | (have j0 := eq477 (k X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq526 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq510 (σ X0) (σ X1)
       grind)
    | exact superpose eq510 eq15
    | (have j1 := eq510 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq826 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq526 x y
       grind)
    | exact superpose eq526 eq16
    | (have j1 := eq526 x y
       grind)
    | exact resolve eq16 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq850 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq826
       have i₂ := eq460 y x
       grind)
    | exact superpose eq460 eq826
    | (have j1 := eq460 (σ x) (σ y)
       grind)
    | (have r₁ := eq826
       have r₂ := eq460 y x
       grind)
    | (have r₁ := eq826
       have r₂ := eq460 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq826
       have r₂ := eq460 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq826 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460 eq826
  have eq851 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq850
  have eq854 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq851
       grind)
    | exact superpose eq851 eq16
    | exact resolve eq16 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq855 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq854
       have i₂ := eq78 (σ x)
       grind)
    | exact superpose eq78 eq854
    | exact resolve eq854 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq856 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq855
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq855
    | exact resolve eq855 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq857 : (σ x) = (σ y) := by grind
  clear eq856
  have eq858 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq857
       grind)
    | exact superpose eq857 eq16
    | exact resolve eq16 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq859 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq857
       grind)
    | exact superpose eq857 eq10
    | exact resolve eq10 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq898 : x = y := by
    first
    | (have i₁ := eq859
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq859
    | exact resolve eq859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq899 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq858
       have i₂ := eq78 (σ x)
       grind)
    | exact superpose eq78 eq858
    | exact resolve eq858 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq900 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq899
       have i₂ := eq898
       grind)
    | exact superpose eq898 eq899
    | exact resolve eq899 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898 eq899
  have eq901 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq900
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq900
    | exact resolve eq900 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq900
  have eq902 : False := by grind
  exact eq902

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_x_pyx_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq76 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x X0)) X2
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76 X0 (M.op X0 x)
       have i₂ := eq76 X0 x
       grind)
    | exact superpose eq76 eq76
    | exact resolve eq76 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq102 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq106 : ∀ X0 X1 : G, (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 X1
       have i₂ := eq79 X1
       grind)
    | exact superpose eq79 eq102
    | (have j0 := eq102 X0 X1
       grind)
    | exact resolve eq102 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq107 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq106 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq110 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 X1
       have i₂ := eq79 (σ X1)
       grind)
    | exact superpose eq79 eq100
    | (have j0 := eq100 X0 X1
       grind)
    | exact resolve eq100 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq111 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq120 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq107 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq107
    | exact resolve eq107 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq141 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq120
    | (have j0 := eq120 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq120 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq273 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq111 x y
       grind)
    | exact superpose eq111 eq16
    | (have j1 := eq111 x y
       grind)
    | exact resolve eq16 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq287 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq273
       have i₂ := eq141 x y
       grind)
    | exact superpose eq141 eq273
    | (have j1 := eq141 (σ x) (σ y)
       grind)
    | (have r₁ := eq273
       have r₂ := eq141 x y
       grind)
    | (have r₁ := eq273
       have r₂ := eq141 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq273
       have r₂ := eq141 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq273 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq273
  have eq288 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq287
  have eq291 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq288
       grind)
    | exact superpose eq288 eq16
    | exact resolve eq16 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq292 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq291
       have i₂ := eq79 (σ x)
       grind)
    | exact superpose eq79 eq291
    | exact resolve eq291 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq293 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq292
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq292
    | exact resolve eq292 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq294 : (σ x) = (σ y) := by grind
  clear eq293
  have eq295 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq294
       grind)
    | exact superpose eq294 eq16
    | exact resolve eq16 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq294
       grind)
    | exact superpose eq294 eq10
    | exact resolve eq10 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq309 : x = y := by
    first
    | (have i₁ := eq296
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq296
    | exact resolve eq296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq310 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq295
       have i₂ := eq79 (σ x)
       grind)
    | exact superpose eq79 eq295
    | exact resolve eq295 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq311 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq310
       have i₂ := eq309
       grind)
    | exact superpose eq309 eq310
    | exact resolve eq310 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq310
  have eq312 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq311
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq311
    | exact resolve eq311 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq311
  have eq313 : False := by grind
  exact eq313

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_pxy_pxy_pxx_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
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
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq43 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq43 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq44 (σ X0)
       grind)
    | exact superpose eq44 eq15
    | exact resolve eq15 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq44 (τ X0)
       grind)
    | exact superpose eq44 eq18
    | exact resolve eq18 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48
    | exact resolve eq48 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq51 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq46
    | exact resolve eq46 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq49
    | exact resolve eq49 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq49
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq72 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X1
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq68
    | (have j0 := eq68 X0 X1
       grind)
    | exact resolve eq68 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq101 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq13
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq109 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq74
    | (have j0 := eq74 X1 X1
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq123 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq109
    | (have j0 := eq109 X0 X1
       grind)
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq127 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq123 X0 X1
       have j1 := eq102 X1 X0
       grind)
    | (have r₁ := eq123 X0 X0
       have r₂ := eq102 X0 X1
       grind)
    | exact resolve eq123 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq461 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq127
    | exact resolve eq127 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq127 (σ X1) X0
       grind)
    | exact superpose eq127 eq15
    | (have j1 := eq127 (σ X1) X0
       grind)
    | exact resolve eq15 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq488 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq461 X0 X1
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq461
    | (have j0 := eq461 X0 X1
       grind)
    | exact resolve eq461 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq461
  have eq499 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq488 X0 (τ X1)
       grind)
    | exact superpose eq488 eq18
    | (have j1 := eq488 X0 (τ X1)
       grind)
    | exact resolve eq18 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq488
  have eq3801 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq499 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq499
    | exact resolve eq499 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq3863 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3801 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3801
    | (have j0 := eq3801 X0 X1
       grind)
    | exact resolve eq3801 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3801
  have eq9833 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq468 x y
       grind)
    | exact superpose eq468 eq16
    | (have j1 := eq468 x y
       grind)
    | exact resolve eq16 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9890 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq468 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq18414 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9833
       have i₂ := eq3863 y x
       grind)
    | exact superpose eq3863 eq9833
    | (have j1 := eq3863 y x
       grind)
    | (have r₁ := eq9833
       have r₂ := eq3863 y x
       grind)
    | exact resolve eq9833 eq3863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9833
  have eq18415 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq18414
  have eq18744 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18415
       grind)
    | exact superpose eq18415 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18415
       grind)
    | exact resolve eq13 eq18415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18415
  have eq18750 : (k x y) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq18744
  have eq77661 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9890 x y
       have i₂ := eq18750
       grind)
    | exact superpose eq18750 eq9890
    | (have j0 := eq9890 x y
       grind)
    | exact resolve eq9890 eq18750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9890 eq18750
  have eq77673 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq77661
  have eq77674 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq77673
  have eq77689 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77674
       grind)
    | exact superpose eq77674 eq16
    | exact resolve eq16 eq77674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77690 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq101 x (σ y)
       have i₂ := eq77674
       grind)
    | exact superpose eq77674 eq101
    | (have j0 := eq101 x (σ y)
       grind)
    | (have r₁ := eq101 x (σ y)
       have r₂ := eq77674
       grind)
    | exact resolve eq101 eq77674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq77674
  have eq77717 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq77690
  have eq77719 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq77717
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq77717
    | exact resolve eq77717 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77717
  have eq77921 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3863 y x
       have i₂ := eq77719
       grind)
    | exact superpose eq77719 eq3863
    | (have j0 := eq3863 y x
       grind)
    | exact resolve eq3863 eq77719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3863 eq77719
  have eq78052 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq77921
       have r₂ := eq77689
       grind)
    | exact resolve eq77921 eq77689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77921
  have eq78286 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq77689
       have i₂ := eq78052
       grind)
    | exact superpose eq78052 eq77689
    | exact resolve eq77689 eq78052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77689 eq78052
  have eq78305 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq78286
  have eq78306 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq78305
  have eq78530 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq78306
       grind)
    | exact superpose eq78306 eq10
    | exact resolve eq10 eq78306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78306
  have eq78654 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq78530
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq78530
    | exact resolve eq78530 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78530
  have eq78655 : x = (M.op x x) := by grind
  clear eq78654
  have eq78669 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq78655
       grind)
    | exact superpose eq78655 eq12
    | (have j0 := eq12 x X0
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq78655
       grind)
    | exact resolve eq12 eq78655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78672 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq102 x X0
       have i₂ := eq78655
       grind)
    | exact superpose eq78655 eq102
    | (have j0 := eq102 x X0
       grind)
    | exact resolve eq102 eq78655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq78655
  have eq78760 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq78672 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78672
  have eq78761 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq78669 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78669
  have eq80677 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq78760 (σ X0)
       grind)
    | exact superpose eq78760 eq15
    | exact resolve eq15 eq78760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78760
  have eq80917 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq80677 X0
       have i₂ := eq78761 X0
       grind)
    | exact superpose eq78761 eq80677
    | exact resolve eq80677 eq78761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78761 eq80677
  have eq83766 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80917 y
       grind)
    | exact superpose eq80917 eq16
    | (have r₁ := eq16
       have r₂ := eq80917 y
       grind)
    | exact resolve eq16 eq80917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80917
  have eq84037 : False := by grind
  exact eq84037

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pxy_x_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq306 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq312 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq294 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq313 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq312 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq314 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq307 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq307 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq307 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq332 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq314 (σ X0)
       grind)
    | exact superpose eq314 eq15
    | exact resolve eq15 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq332 X0
       have i₂ := eq314 X0
       grind)
    | exact superpose eq314 eq332
    | exact resolve eq332 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314 eq332
  have eq400 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq351 X0
       grind)
    | exact superpose eq351 eq63
    | exact resolve eq63 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq313 X0 (τ X1)
       grind)
    | exact superpose eq313 eq19
    | (have j1 := eq313 X0 (τ X1)
       grind)
    | exact resolve eq19 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq482 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq313 (σ X0) (σ X1)
       grind)
    | exact superpose eq313 eq15
    | (have j1 := eq313 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq505 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq482 X0 X1
       have i₂ := eq351 X0
       grind)
    | exact superpose eq351 eq482
    | (have j0 := eq482 X0 X1
       grind)
    | exact resolve eq482 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351 eq482
  have eq614 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq479 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq479
    | exact resolve eq479 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq661 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq614 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq614
    | (have j0 := eq614 X0 X1
       grind)
    | exact resolve eq614 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq1100 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq505 x y
       grind)
    | exact superpose eq505 eq16
    | (have j1 := eq505 x y
       grind)
    | exact resolve eq16 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq1159 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1100
       have i₂ := eq661 y x
       grind)
    | exact superpose eq661 eq1100
    | (have j1 := eq661 y x
       grind)
    | (have r₁ := eq1100
       have r₂ := eq661 y x
       grind)
    | exact resolve eq1100 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq1100
  have eq1160 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1159
  have eq1164 : x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq63 x
       have i₂ := eq1160
       grind)
    | exact superpose eq1160 eq63
    | exact resolve eq63 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1167 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq400 x
       have i₂ := eq1160
       grind)
    | exact superpose eq1160 eq400
    | exact resolve eq400 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq1200 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1167
       grind)
    | exact superpose eq1167 eq16
    | exact resolve eq16 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1224 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1200
       have i₂ := eq1164
       grind)
    | exact superpose eq1164 eq1200
    | exact resolve eq1200 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164 eq1200
  have eq1226 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1224
  have eq1227 : (σ y) = (σ (M.op x x)) := by grind
  clear eq1226
  have eq1232 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq400 x
       have i₂ := eq1227
       grind)
    | exact superpose eq1227 eq400
    | exact resolve eq400 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq1233 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1227
       grind)
    | exact superpose eq1227 eq10
    | exact resolve eq10 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1277 : y = (M.op x x) := by
    first
    | (have i₁ := eq1233
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1233
    | exact resolve eq1233 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq1280 : x = (M.op x y) := by
    first
    | (have i₁ := eq63 x
       have i₂ := eq1277
       grind)
    | exact superpose eq1277 eq63
    | exact resolve eq63 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1277
  have eq1318 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1232
       grind)
    | exact superpose eq1232 eq16
    | exact resolve eq16 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232
  have eq1329 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1318
       have i₂ := eq1280
       grind)
    | exact superpose eq1280 eq1318
    | exact resolve eq1318 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280 eq1318
  have eq1330 : False := by grind
  exact eq1330
