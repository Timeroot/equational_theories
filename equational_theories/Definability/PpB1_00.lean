import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxy_x_pyx_Equation1027 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1027 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxy_y_pxy_Equation1027 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,Y) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxy_pxx_Equation1027 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) Law1027 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq63 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
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
  have eq66 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 X0 (M.op X0 x)
       have i₂ := eq63 X0 x
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq83 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq66 X0
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq84 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq84 (σ X1) (σ X0)
       grind)
    | exact superpose eq84 eq15
    | exact resolve eq15 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq84 X1 X0
       grind)
    | exact superpose eq84 eq87
    | exact resolve eq87 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq87
  have eq266 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq98 x y
       grind)
    | exact superpose eq98 eq16
    | (have r₁ := eq16
       have r₂ := eq98 x y
       grind)
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq274 : False := by grind
  exact eq274

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_x_pyy_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq368 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq376 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
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
  have eq387 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq376 X0 X1
       have i₂ := eq78 X1
       grind)
    | exact superpose eq78 eq376
    | (have j0 := eq376 X0 X1
       grind)
    | exact resolve eq376 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq395 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq78 (σ X1)
       grind)
    | exact superpose eq78 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq410 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq387 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq387
    | exact resolve eq387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq387 X0 (M.op (τ X0) x)
       have i₂ := eq75 (τ X0) x
       grind)
    | exact superpose eq75 eq387
    | (have j0 := eq387 X0 (M.op (τ X0) X1)
       grind)
    | exact resolve eq387 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq438 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq418 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq446 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k X0 (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq438 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq438
    | (have j0 := eq438 X0 X1
       grind)
    | exact resolve eq438 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq450 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq410 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq410
    | (have j0 := eq410 X0 X1
       grind)
    | exact resolve eq410 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq455 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (σ X0) = (k (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq446 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq446
    | exact resolve eq446 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq480 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq455 X0 X1
       have i₂ := eq15 X0 (M.op X0 X1)
       grind)
    | exact superpose eq15 eq455
    | (have j0 := eq455 X0 X1
       grind)
    | exact resolve eq455 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq616 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X1 X0
       have i₂ := eq450 X1 X0
       grind)
    | exact superpose eq450 eq75
    | (have j1 := eq450 X1 X0
       grind)
    | exact resolve eq75 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq695 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq395 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq395
    | exact resolve eq395 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq395 x y
       grind)
    | exact superpose eq395 eq16
    | (have j1 := eq395 x y
       grind)
    | exact resolve eq16 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq726 : ∀ X0 X1 : G, (M.op (σ X1) X0) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq695
    | (have j0 := eq695 X0 X1
       grind)
    | exact resolve eq695 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq695
  have eq1609 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq726 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq726
    | exact resolve eq726 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq1734 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq480 X0 X1
       have i₂ := eq1609 X0 X1
       grind)
    | exact superpose eq1609 eq480
    | (have j1 := eq1609 X1 X0
       grind)
    | exact resolve eq480 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq1745 : ∀ X0 X1 : G, X0 = X1 ∨ (σ X0) = (σ (k X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq616 X1 X0
       have i₂ := eq1609 X0 X1
       grind)
    | exact superpose eq1609 eq616
    | (have j0 := eq616 X0 X1
       have j1 := eq1609 X1 X0
       grind)
    | exact resolve eq616 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq1609
  have eq1780 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1745 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745
  have eq1791 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1734 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq1960 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1780 X1 X0
       have i₂ := eq1791 X1 X0
       grind)
    | exact superpose eq1791 eq1780
    | (have j0 := eq1780 (σ X0) (σ X1)
       have j1 := eq1791 (σ X0) (σ X1)
       grind)
    | exact resolve eq1780 eq1791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780 eq1791
  have eq1988 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1960 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq2065 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq1988 (τ X0) X1
       grind)
    | exact superpose eq1988 eq18
    | (have j1 := eq1988 (τ X0) X1
       grind)
    | exact resolve eq18 eq1988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1988
  have eq2092 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (σ X1) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2065 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2065
    | (have j0 := eq2065 X0 X1
       grind)
    | exact resolve eq2065 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065
  have eq2162 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2092 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2092
    | (have j0 := eq2092 (k (σ X0) (σ X1)) (M.op X0 X1)
       grind)
    | exact resolve eq2092 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2092
  have eq2236 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2162 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2162
    | (have j0 := eq2162 X0 X1
       grind)
    | exact resolve eq2162 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162
  have eq27428 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq700
       have i₂ := eq2236 x y
       grind)
    | exact superpose eq2236 eq700
    | (have j1 := eq2236 x y
       grind)
    | (have r₁ := eq700
       have r₂ := eq2236 x y
       grind)
    | (have r₁ := eq700
       have r₂ := eq2236 (M.op x y) (k x y)
       grind)
    | (have r₁ := eq700
       have r₂ := eq2236 (k x y) (M.op x y)
       grind)
    | exact resolve eq700 eq2236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700 eq2236
  have eq27435 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27428
  have eq27436 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq27435
  have eq27454 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq16
    | exact resolve eq16 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27436
  have eq27455 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27454
       have i₂ := eq78 (σ x)
       grind)
    | exact superpose eq78 eq27454
    | exact resolve eq27454 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27454
  have eq27456 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27455
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq27455
    | exact resolve eq27455 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27455
  have eq27457 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq27456
  have eq27459 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq27457
       grind)
    | exact superpose eq27457 eq10
    | exact resolve eq10 eq27457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27457
  have eq27522 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27459
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq27459
    | exact resolve eq27459 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27459
  have eq27524 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27522
       grind)
    | exact superpose eq27522 eq16
    | exact resolve eq16 eq27522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27522
  have eq27525 : (σ x) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27524
       have i₂ := eq78 (σ x)
       grind)
    | exact superpose eq78 eq27524
    | exact resolve eq27524 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27524
  have eq27526 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27525
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq27525
    | exact resolve eq27525 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27525
  have eq27527 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq27526
  have eq27543 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27527
       grind)
    | exact superpose eq27527 eq16
    | exact resolve eq16 eq27527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27553 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75 (σ x) (σ y)
       have i₂ := eq27527
       grind)
    | exact superpose eq27527 eq75
    | exact resolve eq75 eq27527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq27716 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq27527
       have i₂ := eq27553
       grind)
    | exact superpose eq27553 eq27527
    | exact resolve eq27527 eq27553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27527 eq27553
  have eq27781 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq27716
       grind)
    | exact superpose eq27716 eq10
    | exact resolve eq10 eq27716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27716
  have eq27844 : x = y := by
    first
    | (have i₁ := eq27781
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq27781
    | exact resolve eq27781 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27781
  have eq27848 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq27543
       have i₂ := eq27844
       grind)
    | exact superpose eq27844 eq27543
    | exact resolve eq27543 eq27844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27543 eq27844
  have eq27850 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq27848
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq27848
    | exact resolve eq27848 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq27848
  have eq27851 : False := by grind
  exact eq27851

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxy_pxx_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
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
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq102 : ∀ X0 X1 : G, (M.op (k (τ X0) X1) (k (τ X0) X1)) = (τ (M.op (k X0 (σ X1)) (k X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (k X0 (σ X1))
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq63
    | exact resolve eq63 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
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
  have eq169 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq170 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq2484 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq169 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq169
    | exact resolve eq169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq2529 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2484 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2484
    | (have j0 := eq2484 X0 X1
       grind)
    | exact resolve eq2484 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2484
  have eq2575 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 X1)) = (τ (k X2 (σ (M.op X0 X1)))) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X2 (k X0 X1)
       have i₂ := eq2529 X1 X0
       grind)
    | exact superpose eq2529 eq28
    | (have j1 := eq2529 X1 X0
       grind)
    | exact resolve eq28 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2580 : ∀ X0 X1 X2 : G, (k (k X0 X1) (τ X2)) = (τ (k (σ (M.op X0 X1)) X2)) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37 (k X0 X1) X2
       have i₂ := eq2529 X1 X0
       grind)
    | exact superpose eq2529 eq37
    | (have j1 := eq2529 X1 X0
       grind)
    | exact resolve eq37 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529
  have eq2601 : ∀ X0 X1 X2 : G, (k (k X0 X1) (τ X2)) = (k (M.op X0 X1) (τ X2)) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2580 X0 X1 X2
       have i₂ := eq37 (M.op X0 X1) X2
       grind)
    | exact superpose eq37 eq2580
    | (have j0 := eq2580 X0 X1 X2
       grind)
    | exact resolve eq2580 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2580
  have eq2606 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 X1)) = (k (τ X2) (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2575 X0 X1 X2
       have i₂ := eq28 X2 (M.op X0 X1)
       grind)
    | exact superpose eq28 eq2575
    | (have j0 := eq2575 X0 X1 X2
       grind)
    | exact resolve eq2575 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2575
  have eq3352 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq170 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq5432 : ∀ X0 : G, (M.op (k (τ (σ X0)) X0) (k (τ (σ X0)) X0)) = (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq102
  have eq5530 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (k (τ (σ X0)) X0) (k (τ (σ X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq5432 X0
       have i₂ := eq114 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq114 eq5432
    | exact resolve eq5432 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5432
  have eq5601 : ∀ X0 : G, (k (τ (σ X0)) X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5530 X0
       have i₂ := eq114 (k (τ (σ X0)) X0)
       grind)
    | exact superpose eq114 eq5530
    | exact resolve eq5530 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5530
  have eq5657 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq5601 X0
       have i₂ := eq114 (σ X0)
       grind)
    | exact superpose eq114 eq5601
    | exact resolve eq5601 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5601
  have eq5682 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5657 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5657
    | exact resolve eq5657 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5657
  have eq21054 : ∀ X0 X1 X2 : G, (M.op X1 X2) = X1 ∨ (k (k X1 X2) X0) = (k (M.op X1 X2) X0) ∨ X1 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2601 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2601
    | (have j0 := eq2601 X1 X2 X2
       grind)
    | exact resolve eq2601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2601
  have eq21220 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (k X0 X1) X2) = (k (M.op X0 X1) X2) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq21054 X2 X0 X1
       grind)
    | exact superpose eq21054 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq21054 X2 X0 X1
       grind)
    | (have r₁ := eq13 X1 X2
       have r₂ := eq21054 X0 X1 X2
       grind)
    | (have r₁ := eq13 X2 X1
       have r₂ := eq21054 X0 (M.op X2 X1) X2
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq21054 X0 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq21054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21054
  have eq21273 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (k X0 X1) X2) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq21220 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21220
  have eq21274 : ∀ X0 X1 X2 : G, X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (k X0 X1) X2) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq21273 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21273
  have eq21289 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (k (M.op X0 X1) X2) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21274 X0 X1 X2
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq21274
    | (have j0 := eq21274 X0 X1 X2
       grind)
    | exact resolve eq21274 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21274
  have eq21392 : ∀ X0 X1 : G, (k X0 X1) = (k (M.op X0 X1) (k X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5682 (k X0 X1)
       have i₂ := eq21289 X0 X1 (k X0 X1)
       grind)
    | exact superpose eq21289 eq5682
    | (have j1 := eq21289 X0 X1 x
       grind)
    | exact resolve eq5682 eq21289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5682 eq21289
  have eq21775 : ∀ X0 X1 X2 : G, (M.op X1 X2) = X1 ∨ (k X0 (k X1 X2)) = (k X0 (M.op X1 X2)) ∨ X1 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2606 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2606
    | (have j0 := eq2606 X1 X2 X2
       grind)
    | exact resolve eq2606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2606
  have eq22040 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X2 (k X0 X1)) = (k X2 (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq21775 X2 X0 X1
       grind)
    | exact superpose eq21775 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq21775 X2 X0 X1
       grind)
    | (have r₁ := eq13 X1 X2
       have r₂ := eq21775 X0 X1 X2
       grind)
    | (have r₁ := eq13 X2 X1
       have r₂ := eq21775 X0 (M.op X2 X1) X2
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq21775 X0 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq21775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21775
  have eq22095 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X2 (k X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq22040 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22040
  have eq22096 : ∀ X0 X1 X2 : G, X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X2 (k X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq22095 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22095
  have eq22111 : ∀ X0 X1 X2 : G, (k X2 (k X0 X1)) = (k X2 (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22096 X0 X1 X2
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq22096
    | (have j0 := eq22096 X0 X1 X2
       grind)
    | exact resolve eq22096 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22096
  have eq22229 : ∀ X0 X1 : G, (k X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21392 X0 X1
       have i₂ := eq22111 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq22111 eq21392
    | (have j0 := eq21392 X0 X1
       have j1 := eq22111 X0 X1 x
       grind)
    | exact resolve eq21392 eq22111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21392 eq22111
  have eq22286 : ∀ X0 X1 : G, (k X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq22229 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22229
  have eq22345 : ∀ X0 X1 : G, (k X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  clear eq22286
  have eq22351 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22345 X0 X1
       have i₂ := eq114 (M.op X0 X1)
       grind)
    | exact superpose eq114 eq22345
    | (have j0 := eq22345 X0 X1
       grind)
    | exact resolve eq22345 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22345
  have eq22443 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq22351 X0 (σ X1)
       grind)
    | exact superpose eq22351 eq28
    | (have j1 := eq22351 (k X0 (σ X1)) X0
       grind)
    | exact resolve eq28 eq22351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq22462 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq22351 X0 (τ X1)
       grind)
    | exact superpose eq22351 eq19
    | (have j1 := eq22351 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq22351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq22351
  have eq23517 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq22443 (σ X0) X1
       grind)
    | exact superpose eq22443 eq37
    | (have j1 := eq22443 (σ X1) X0
       grind)
    | exact resolve eq37 eq22443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq22443
  have eq23592 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23517 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq23517
    | (have j0 := eq23517 X0 X1
       grind)
    | exact resolve eq23517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23517
  have eq23628 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23592 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23592
    | (have j0 := eq23592 X0 X1
       grind)
    | exact resolve eq23592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23592
  have eq23642 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23628 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23628
    | (have j0 := eq23628 X0 X1
       grind)
    | exact resolve eq23628 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23628
  have eq23899 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22462 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22462
    | exact resolve eq22462 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22462
  have eq24046 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23899 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq23899
    | (have j0 := eq23899 X0 X1
       grind)
    | exact resolve eq23899 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23899
  have eq24402 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq23642 X0 X1
       grind)
    | exact superpose eq23642 eq11
    | (have j1 := eq23642 X0 X1
       grind)
    | exact resolve eq11 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23642
  have eq26885 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24402 x y
       grind)
    | exact superpose eq24402 eq16
    | (have j1 := eq24402 x y
       grind)
    | exact resolve eq16 eq24402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24402
  have eq27167 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq26885
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq26885
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq26885
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq26885
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq26885 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27168 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq26885
       have i₂ := eq24046 y x
       grind)
    | exact superpose eq24046 eq26885
    | (have j1 := eq24046 x (k x y)
       grind)
    | (have r₁ := eq26885
       have r₂ := eq24046 y x
       grind)
    | (have r₁ := eq26885
       have r₂ := eq24046 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq26885
       have r₂ := eq24046 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq26885 eq24046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24046 eq26885
  have eq27176 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27168
  have eq27177 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq27176
  have eq27178 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27167
  have eq27179 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq27178
  have eq27183 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27177
       grind)
    | exact superpose eq27177 eq16
    | exact resolve eq16 eq27177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27177
  have eq27198 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq27183
       have r₂ := eq22 x
       grind)
    | exact resolve eq27183 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27183
  have eq27212 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3352 x y
       have i₂ := eq27198
       grind)
    | exact superpose eq27198 eq3352
    | (have j0 := eq3352 x y
       grind)
    | exact resolve eq3352 eq27198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352 eq27198
  have eq27218 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq27212
  have eq27219 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27218
  have eq27225 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27179
       grind)
    | exact superpose eq27179 eq16
    | exact resolve eq16 eq27179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27179
  have eq27240 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27225
       have r₂ := eq22 x
       grind)
    | exact resolve eq27225 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27225
  have eq27243 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq27240
       grind)
    | exact superpose eq27240 eq10
    | exact resolve eq10 eq27240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27240
  have eq27320 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27243
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq27243
    | exact resolve eq27243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27243
  have eq27327 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27320
       grind)
    | exact superpose eq27320 eq16
    | exact resolve eq16 eq27320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27320
  have eq27342 : x = (M.op x y) := by
    first
    | (have r₁ := eq27327
       have r₂ := eq22 x
       grind)
    | exact resolve eq27327 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq27327
  have eq28234 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27219
       grind)
    | exact superpose eq27219 eq16
    | exact resolve eq16 eq27219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27219
  have eq28319 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28234
       have i₂ := eq114 (σ x)
       grind)
    | exact superpose eq114 eq28234
    | exact resolve eq28234 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq28234
  have eq28325 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28319
       have i₂ := eq27342
       grind)
    | exact superpose eq27342 eq28319
    | exact resolve eq28319 eq27342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28319
  have eq28326 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28325
  have eq28349 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28326
       grind)
    | exact superpose eq28326 eq16
    | exact resolve eq16 eq28326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28326
  have eq28392 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq28349
       have i₂ := eq27342
       grind)
    | exact superpose eq27342 eq28349
    | exact resolve eq28349 eq27342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27342 eq28349
  have eq28393 : False := by grind
  exact eq28393

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_x_pxx_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
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

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_y_pxy_y_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq22
  have eq62 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq278 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq278 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq281 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq279 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq279 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq279 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq292 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq281 (σ X0)
       grind)
    | exact superpose eq281 eq15
    | exact resolve eq15 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq281 (τ X0)
       grind)
    | exact superpose eq281 eq31
    | exact resolve eq31 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq305 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq298 X0
       have i₂ := eq281 X0
       grind)
    | exact superpose eq281 eq298
    | exact resolve eq298 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq311 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq292 X0
       have i₂ := eq281 X0
       grind)
    | exact superpose eq281 eq292
    | exact resolve eq292 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq292
  have eq357 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq311 X0
       grind)
    | exact superpose eq311 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq311 X0
       grind)
    | exact superpose eq311 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq62 (σ X0)
       have i₂ := eq311 X0
       grind)
    | exact superpose eq311 eq62
    | exact resolve eq62 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq360 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq357 X0 X1
       have j1 := eq358 X0 X1
       grind)
    | (have r₁ := eq357 X0 X1
       have r₂ := eq358 X0 X1
       grind)
    | exact resolve eq357 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq358
  have eq498 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq360 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq360
    | exact resolve eq360 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) X2) = X2 ∨ (k (k X0 (σ X1)) X2) = (M.op (k X0 (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq360 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq360
    | exact resolve eq360 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq360 X0 (σ X1)
       grind)
    | exact superpose eq360 eq15
    | (have j1 := eq360 X0 (σ X1)
       grind)
    | exact resolve eq15 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq360 X0 X1
       grind)
    | exact superpose eq360 eq28
    | (have j1 := eq360 X0 X1
       grind)
    | exact resolve eq28 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq360
  have eq549 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq498 (τ X0) X1
       grind)
    | exact superpose eq498 eq17
    | (have j1 := eq498 (τ X0) X1
       grind)
    | exact resolve eq17 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq614 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X0 X0)))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq509 X0 (σ (M.op X0 X0))
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq509
    | exact resolve eq509 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq509
  have eq642 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq614 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq614
    | (have j0 := eq614 X0
       grind)
    | exact resolve eq614 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq650 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq642 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq642
    | (have j0 := eq642 X0
       grind)
    | exact resolve eq642 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq710 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq650 (τ X0)
       grind)
    | exact superpose eq650 eq17
    | (have j1 := eq650 (τ X0)
       grind)
    | exact resolve eq17 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq650
  have eq715 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op X0 X0)))) ∨ (σ (τ X0)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq710 X0
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq710
    | (have j0 := eq710 X0
       grind)
    | exact resolve eq710 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq725 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (σ (τ X0)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq715 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq715
    | (have j0 := eq715 X0
       grind)
    | exact resolve eq715 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq732 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ (τ X0)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq725 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq725
    | (have j0 := eq725 X0
       grind)
    | exact resolve eq725 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq739 : ∀ X0 : G, (σ (τ X0)) = (σ (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq732 X0
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq732
    | (have j0 := eq732 X0
       grind)
    | exact resolve eq732 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq732
  have eq745 : ∀ X0 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq739 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq739
    | (have j0 := eq739 X0
       grind)
    | exact resolve eq739 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq746 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq745 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq745
    | (have j0 := eq745 X0
       grind)
    | exact resolve eq745 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq752 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq746 X0
       grind)
    | exact superpose eq746 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq746 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq746 X0
       grind)
    | exact resolve eq12 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq764 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq752 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq832 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq764 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq833 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq832 X0
       grind)
    | (have r₁ := eq832 X0
       have r₂ := eq62 X0
       grind)
    | exact resolve eq832 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq844 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq833 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq833
    | exact resolve eq833 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq833
  have eq972 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq549 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq549
    | exact resolve eq549 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq1037 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq972 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq972
    | (have j0 := eq972 X0 X1
       grind)
    | exact resolve eq972 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq1746 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq504 x y
       grind)
    | exact superpose eq504 eq16
    | (have j1 := eq504 x y
       grind)
    | exact resolve eq16 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1780 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq504 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq2051 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1746
       have i₂ := eq1037 x y
       grind)
    | exact superpose eq1037 eq1746
    | (have j1 := eq1037 (σ x) (σ y)
       grind)
    | (have r₁ := eq1746
       have r₂ := eq1037 x y
       grind)
    | exact resolve eq1746 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746
  have eq2052 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2051
  have eq11249 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (k (k X1 (σ X2)) X0) = X0 ∨ (k (k X1 (σ X2)) X0) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X1 (σ X2)) X0
       have i₂ := eq499 X1 X2 X0
       grind)
    | exact superpose eq499 eq13
    | (have j0 := eq13 (k X1 (σ X2)) X0
       have j1 := eq499 X1 X2 (k X1 (σ X2))
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) X2
       have r₂ := eq499 X0 X1 X2
       grind)
    | exact resolve eq13 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq11256 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (k (k X1 (σ X2)) X0) = X0 ∨ (k (k X1 (σ X2)) X0) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq11249 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11249
  have eq11265 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) X0) = (M.op (k X1 (σ X2)) X0) ∨ (k (k X1 (σ X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq11256 X0 X1 X2
       have j1 := eq12 (k X1 (σ X2)) X0
       grind)
    | (have r₁ := eq11256 X0 X1 X2
       have r₂ := eq12 (k X1 (σ X2)) X1
       grind)
    | exact resolve eq11256 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11256
  have eq17635 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) X2) ≠ X2 ∨ (k (k X0 (σ X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq11265 X2 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11265
  have eq17943 : ∀ X0 X1 X2 : G, (M.op (k X1 X0) X2) ≠ X2 ∨ (k (k X1 X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17635 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17635
    | exact resolve eq17635 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17635
  have eq18020 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17943 (M.op X0 X0) X0 x
       have i₂ := eq844 X0
       grind)
    | exact superpose eq844 eq17943
    | exact resolve eq17943 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq17943
  have eq18132 : y ≠ y ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18020 x y
       have i₂ := eq2052
       grind)
    | exact superpose eq2052 eq18020
    | (have j0 := eq18020 x y
       grind)
    | (have r₁ := eq18020 x y
       have r₂ := eq2052
       grind)
    | (have r₁ := eq18020 (σ x) (σ y)
       have r₂ := eq2052
       grind)
    | exact resolve eq18020 eq2052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq18134 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18132
  have eq18216 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1780 x y
       have i₂ := eq18134
       grind)
    | exact superpose eq18134 eq1780
    | (have j0 := eq1780 x y
       grind)
    | exact resolve eq1780 eq18134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780 eq18134
  have eq18242 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18216
  have eq18243 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18242
  have eq18250 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18243
       grind)
    | exact superpose eq18243 eq16
    | exact resolve eq16 eq18243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18255 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq18020 (σ x) (σ y)
       have i₂ := eq18243
       grind)
    | exact superpose eq18243 eq18020
    | (have j0 := eq18020 (σ x) (σ y)
       grind)
    | (have r₁ := eq18020 (σ x) (σ y)
       have r₂ := eq18243
       grind)
    | exact resolve eq18020 eq18243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18020 eq18243
  have eq18256 : (σ y) = (k (σ x) (σ y)) := by grind
  clear eq18255
  have eq18258 : (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq18256
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq18256
    | exact resolve eq18256 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18256
  have eq18276 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1037 x y
       have i₂ := eq18258
       grind)
    | exact superpose eq18258 eq1037
    | (have j0 := eq1037 x y
       grind)
    | exact resolve eq1037 eq18258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037 eq18258
  have eq18365 : y = (M.op x y) := by
    first
    | (have r₁ := eq18276
       have r₂ := eq18250
       grind)
    | exact resolve eq18276 eq18250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18276
  have eq18413 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq18250
       have i₂ := eq18365
       grind)
    | exact superpose eq18365 eq18250
    | exact resolve eq18250 eq18365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18250 eq18365
  have eq18423 : False := by grind
  exact eq18423

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyy_pyy_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq23
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq71 (σ X0)
       grind)
    | exact superpose eq71 eq15
    | exact resolve eq15 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq71 (τ X0)
       grind)
    | exact superpose eq71 eq32
    | exact resolve eq32 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq76 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq76
    | exact resolve eq76 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq85 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq74
    | exact resolve eq74 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq74
  have eq102 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X0)
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq12
    | exact resolve eq12 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq510 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
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
  have eq519 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq502 X0 X1
       have i₂ := eq85 X1
       grind)
    | exact superpose eq85 eq502
    | (have j0 := eq502 X0 X1
       grind)
    | exact resolve eq502 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq558 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq519 x y
       grind)
    | exact superpose eq519 eq16
    | (have j1 := eq519 x y
       grind)
    | exact resolve eq16 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq519 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq3292 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq510 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq510
    | exact resolve eq510 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq3360 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3292 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3292
    | (have j0 := eq3292 X0 X1
       grind)
    | exact resolve eq3292 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3292
  have eq6830 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq558
       have i₂ := eq3360 x y
       grind)
    | exact superpose eq3360 eq558
    | (have j1 := eq3360 x y
       grind)
    | (have r₁ := eq558
       have r₂ := eq3360 x y
       grind)
    | (have r₁ := eq558
       have r₂ := eq3360 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq558
       have r₂ := eq3360 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq558 eq3360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3360
  have eq6831 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq6830
  have eq6844 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq562 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq562
    | (have j0 := eq562 (τ X0) (τ X1)
       grind)
    | exact resolve eq562 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq6909 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X1 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6844 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq6844
    | (have j0 := eq6844 X0 X1
       grind)
    | exact resolve eq6844 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6844
  have eq6943 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6909 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq6909
    | (have j0 := eq6909 X0 X1
       grind)
    | exact resolve eq6909 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6909
  have eq6972 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6943 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6943
    | (have j0 := eq6943 X0 X1
       grind)
    | exact resolve eq6943 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6943
  have eq6997 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6972 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6972
    | (have j0 := eq6972 X0 X1
       grind)
    | exact resolve eq6972 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6972
  have eq7018 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (σ (τ (M.op X1 X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6997 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq6997
    | (have j0 := eq6997 X0 X1
       grind)
    | exact resolve eq6997 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq6997
  have eq7038 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7018 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq7018
    | (have j0 := eq7018 X0 X1
       grind)
    | exact resolve eq7018 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7018
  have eq7053 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7038 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7038
    | (have j0 := eq7038 X0 X1
       grind)
    | exact resolve eq7038 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7038
  have eq7067 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7053 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7053
    | (have j0 := eq7053 X0 X1
       grind)
    | exact resolve eq7053 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7053
  have eq7076 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7067 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7067
    | (have j0 := eq7067 X0 X1
       grind)
    | exact resolve eq7067 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7067
  have eq17724 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6831
       grind)
    | exact superpose eq6831 eq16
    | exact resolve eq16 eq6831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6831
  have eq17725 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq17724
       have r₂ := eq85 x
       grind)
    | exact resolve eq17724 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17724
  have eq17730 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq102 y (σ x)
       have i₂ := eq17725
       grind)
    | exact superpose eq17725 eq102
    | (have j0 := eq102 y (σ x)
       grind)
    | (have r₁ := eq102 y (σ x)
       have r₂ := eq17725
       grind)
    | exact resolve eq102 eq17725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17725
  have eq17733 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq17730
  have eq17737 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq17733
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17733
    | exact resolve eq17733 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17733
  have eq17747 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k X0 y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq17737
       grind)
    | exact superpose eq17737 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq17737
       grind)
    | exact resolve eq12 eq17737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17737
  have eq581872 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have j0 := eq17747 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17747
  have eq584346 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq558
       have i₂ := eq581872
       grind)
    | exact superpose eq581872 eq558
    | exact resolve eq558 eq581872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq581872
  have eq584434 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq584346
  have eq584435 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq584434
  have eq584439 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq562 x y
       grind)
    | (have r₁ := eq584435
       have r₂ := eq562 x y
       grind)
    | exact resolve eq584435 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq584435
  have eq584441 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq584439
       grind)
    | exact superpose eq584439 eq16
    | exact resolve eq16 eq584439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584451 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq102 y (σ x)
       have i₂ := eq584439
       grind)
    | exact superpose eq584439 eq102
    | (have j0 := eq102 y (σ x)
       grind)
    | (have r₁ := eq102 y (σ x)
       have r₂ := eq584439
       grind)
    | exact resolve eq102 eq584439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq584439
  have eq584491 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq584451
  have eq584506 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq584491
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq584491
    | exact resolve eq584491 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584491
  have eq584708 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq584506
       grind)
    | exact superpose eq584506 eq10
    | exact resolve eq10 eq584506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584506
  have eq585062 : (σ (k x y)) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq584708
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq584708
    | exact resolve eq584708 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584708
  have eq585103 : (k x y) = (τ (σ (M.op y y))) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq585062
       grind)
    | exact superpose eq585062 eq10
    | exact resolve eq10 eq585062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585062
  have eq585450 : (k x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq585103
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq585103
    | exact resolve eq585103 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585103
  have eq585509 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq7076 x y
       have i₂ := eq585450
       grind)
    | exact superpose eq585450 eq7076
    | (have j0 := eq7076 x y
       grind)
    | (have r₁ := eq7076 x y
       have r₂ := eq585450
       grind)
    | exact resolve eq7076 eq585450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7076 eq585450
  have eq585653 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq585509
  have eq585654 : (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq585653
  have eq585734 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq584441
       have i₂ := eq585654
       grind)
    | exact superpose eq585654 eq584441
    | exact resolve eq584441 eq585654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584441 eq585654
  have eq586078 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq585734
  have eq586146 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq586078
       grind)
    | exact superpose eq586078 eq10
    | exact resolve eq10 eq586078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586078
  have eq586497 : x = y ∨ x = y := by
    first
    | (have i₁ := eq586146
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq586146
    | exact resolve eq586146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586146
  have eq586498 : x = y := by grind
  clear eq586497
  have eq586503 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq586498
       grind)
    | exact superpose eq586498 eq16
    | exact resolve eq16 eq586498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586498
  have eq586981 : False := by grind
  exact eq586981
