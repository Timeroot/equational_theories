import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,Y) = X then X else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxy_x_pyy_Equation1027 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then X else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_x_y_Equation1027 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) Law1027 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = b :=
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
  have eq64 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
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
  have eq69 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq64 X0 (M.op X0 x)
       have i₂ := eq64 X0 x
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq87 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq69 X0
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq90 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq90 (σ X1) (σ X0)
       grind)
    | exact superpose eq90 eq15
    | exact resolve eq15 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 X1
       have i₂ := eq90 X1 X0
       grind)
    | exact superpose eq90 eq93
    | exact resolve eq93 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq93
  have eq283 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq104 x y
       grind)
    | exact superpose eq104 eq16
    | (have r₁ := eq16
       have r₂ := eq104 x y
       grind)
    | exact resolve eq16 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq292 : False := by grind
  exact eq292

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then Y else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_y_x_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq102 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq104 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = X1 := by
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
  have eq108 : ∀ X0 X1 : G, (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq79 (τ X0)
       grind)
    | exact superpose eq79 eq104
    | (have j0 := eq104 X0 X1
       grind)
    | exact resolve eq104 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq109 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq112 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 X1
       have i₂ := eq79 (σ X0)
       grind)
    | exact superpose eq79 eq102
    | (have j0 := eq102 X0 X1
       grind)
    | exact resolve eq102 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq112 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq122 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq109 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq109
    | exact resolve eq109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq143 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq122 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq122
    | (have j0 := eq122 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq122 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq287 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq113 x y
       grind)
    | exact superpose eq113 eq16
    | (have j1 := eq113 x y
       grind)
    | exact resolve eq16 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq301 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq287
       have i₂ := eq143 x y
       grind)
    | exact superpose eq143 eq287
    | (have j1 := eq143 (σ x) (σ y)
       grind)
    | (have r₁ := eq287
       have r₂ := eq143 x y
       grind)
    | (have r₁ := eq287
       have r₂ := eq143 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq287
       have r₂ := eq143 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq287 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq287
  have eq302 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq301
  have eq305 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq302
       grind)
    | exact superpose eq302 eq16
    | exact resolve eq16 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq306 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq305
       have i₂ := eq79 (σ x)
       grind)
    | exact superpose eq79 eq305
    | exact resolve eq305 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq307 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq306
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq306
    | exact resolve eq306 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq308 : (σ x) = (σ y) := by grind
  clear eq307
  have eq309 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq308
       grind)
    | exact superpose eq308 eq16
    | exact resolve eq16 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq308
       grind)
    | exact superpose eq308 eq10
    | exact resolve eq10 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq323 : x = y := by
    first
    | (have i₁ := eq310
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq310
    | exact resolve eq310 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq324 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq309
       have i₂ := eq79 (σ x)
       grind)
    | exact superpose eq79 eq309
    | exact resolve eq309 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq325 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq324
       have i₂ := eq323
       grind)
    | exact superpose eq323 eq324
    | exact resolve eq324 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq324
  have eq326 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq325
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq325
    | exact resolve eq325 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq325
  have eq327 : False := by grind
  exact eq327

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq593 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4016 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq593 X0 X1
       grind)
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq593 X0 X1
       grind)
    | exact superpose eq593 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq593 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq593 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq593 X0 X1
       grind)
    | exact resolve eq13 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq4021 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4016 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4016
  have eq4022 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4021 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4021
  have eq5551 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq4022 X0 X1
       grind)
    | exact superpose eq4022 eq28
    | (have j1 := eq4022 X0 X1
       grind)
    | exact resolve eq28 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4022
  have eq5590 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5551 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5551
  have eq5618 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5590 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5590
    | exact resolve eq5590 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5590
  have eq5724 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5618 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq5618
    | (have j0 := eq5618 (τ (k X1 X0)) (τ (M.op X1 X0))
       grind)
    | exact resolve eq5618 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq5618
  have eq5770 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq5724 X1 X0
       grind)
    | exact superpose eq5724 eq11
    | (have j1 := eq5724 (k X0 X1) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq5724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5724
  have eq5889 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5770 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq5770
    | (have j0 := eq5770 (k X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq5770 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5770
  have eq5930 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq5889 X0 (τ X1)
       grind)
    | exact superpose eq5889 eq19
    | (have j1 := eq5889 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq5889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq5953 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq5889 (σ X0) (σ X1)
       grind)
    | exact superpose eq5889 eq15
    | (have j1 := eq5889 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq5889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5889
  have eq6242 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5930 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5930
    | exact resolve eq5930 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5930
  have eq6309 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6242 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq6242
    | (have j0 := eq6242 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq6242 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6242
  have eq6757 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5953 x y
       grind)
    | exact superpose eq5953 eq16
    | (have j1 := eq5953 x y
       grind)
    | exact resolve eq16 eq5953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5953
  have eq6842 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6757
       have i₂ := eq6309 y x
       grind)
    | exact superpose eq6309 eq6757
    | (have j1 := eq6309 (σ x) (σ y)
       grind)
    | (have r₁ := eq6757
       have r₂ := eq6309 y x
       grind)
    | (have r₁ := eq6757
       have r₂ := eq6309 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6757
       have r₂ := eq6309 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6757 eq6309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6309 eq6757
  have eq6845 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq6842
  have eq6848 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6845
       grind)
    | exact superpose eq6845 eq16
    | exact resolve eq16 eq6845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6845
  have eq6849 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq6848
       have r₂ := eq22 x
       grind)
    | exact resolve eq6848 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6848
  have eq6850 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6849
       grind)
    | exact superpose eq6849 eq16
    | exact resolve eq16 eq6849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6851 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6849
       grind)
    | exact superpose eq6849 eq10
    | exact resolve eq10 eq6849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6849
  have eq6906 : x = y := by
    first
    | (have i₁ := eq6851
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6851
    | exact resolve eq6851 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6851
  have eq6907 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq6850
       have i₂ := eq114 (σ x)
       grind)
    | exact superpose eq114 eq6850
    | exact resolve eq6850 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6850
  have eq6912 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6907
       have i₂ := eq6906
       grind)
    | exact superpose eq6906 eq6907
    | exact resolve eq6907 eq6906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6906 eq6907
  have eq6916 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq6912
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq6912
    | exact resolve eq6912 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq6912
  have eq6917 : False := by grind
  exact eq6917

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxy_pxx_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq147 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq148 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq814 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq147 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq147
    | exact resolve eq147 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (τ X1)
       have i₂ := eq147 X0 X1
       grind)
    | exact superpose eq147 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq147 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq147 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X1
       have r₂ := eq147 (M.op X1 (τ X1)) X1
       grind)
    | exact resolve eq13 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq840 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq828 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq841 : ∀ X0 X1 : G, (τ X1) = X0 ∨ (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq840 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq848 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 := by
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
  have eq854 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq814 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq814
    | (have j0 := eq814 X0 X1
       grind)
    | exact resolve eq814 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq925 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
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
  have eq2297 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq848 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq848
    | exact resolve eq848 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq2340 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2297 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2297
    | (have j0 := eq2297 X0 X1
       grind)
    | exact resolve eq2297 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297
  have eq2379 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2340 X1 X0
       grind)
    | exact superpose eq2340 eq10
    | (have j1 := eq2340 (k X0 X1) (τ (σ (M.op X0 X1)))
       grind)
    | exact resolve eq10 eq2340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2419 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2379 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2379
    | (have j0 := eq2379 X0 X1
       grind)
    | exact resolve eq2379 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2379
  have eq2432 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq2419 X0 (σ X1)
       grind)
    | exact superpose eq2419 eq28
    | (have j1 := eq2419 (k X0 (σ X1)) X0
       grind)
    | exact resolve eq28 eq2419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2419
  have eq6207 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq2432 (σ X0) X1
       grind)
    | exact superpose eq2432 eq37
    | (have j1 := eq2432 (σ X1) X0
       grind)
    | exact resolve eq37 eq2432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2432
  have eq6257 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6207 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq6207
    | (have j0 := eq6207 X0 X1
       grind)
    | exact resolve eq6207 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6207
  have eq6291 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6257 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6257
    | (have j0 := eq6257 X0 X1
       grind)
    | exact resolve eq6257 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6257
  have eq6304 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6291 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6291
    | (have j0 := eq6291 X0 X1
       grind)
    | exact resolve eq6291 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6291
  have eq6678 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq6304 X0 X1
       grind)
    | exact superpose eq6304 eq11
    | (have j1 := eq6304 X0 X1
       grind)
    | exact resolve eq11 eq6304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6304
  have eq8483 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6678 x y
       grind)
    | exact superpose eq6678 eq16
    | (have j1 := eq6678 x y
       grind)
    | exact resolve eq16 eq6678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6678
  have eq8866 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq8483
       have i₂ := eq2340 y x
       grind)
    | exact superpose eq2340 eq8483
    | (have j1 := eq2340 x (k x y)
       grind)
    | (have r₁ := eq8483
       have r₂ := eq2340 y x
       grind)
    | (have r₁ := eq8483
       have r₂ := eq2340 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8483
       have r₂ := eq2340 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8483 eq2340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2340 eq8483
  have eq8869 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8866
  have eq8870 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq8869
  have eq8876 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8870
       grind)
    | exact superpose eq8870 eq16
    | exact resolve eq16 eq8870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8870
  have eq8877 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8876
       have r₂ := eq22 x
       grind)
    | exact resolve eq8876 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8876
  have eq8995 : x = y ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq854 y x
       have i₂ := eq8877
       grind)
    | exact superpose eq8877 eq854
    | (have j0 := eq854 y x
       grind)
    | exact resolve eq854 eq8877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq14276 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq925
       have i₂ := eq8877
       grind)
    | exact superpose eq8877 eq925
    | exact resolve eq925 eq8877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925 eq8877
  have eq14292 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq14276
  have eq15042 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8995
       grind)
    | exact superpose eq8995 eq16
    | exact resolve eq16 eq8995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8995
  have eq15057 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq15042
       have r₂ := eq22 x
       grind)
    | exact resolve eq15042 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15042
  have eq15069 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109 y x
       have i₂ := eq15057
       grind)
    | exact superpose eq15057 eq109
    | exact resolve eq109 eq15057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15100 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15057
       have i₂ := eq15069
       grind)
    | exact superpose eq15069 eq15057
    | exact resolve eq15057 eq15069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15057 eq15069
  have eq15124 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq15100
  have eq15128 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15124
       grind)
    | exact superpose eq15124 eq16
    | exact resolve eq16 eq15124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15124
  have eq15143 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq15128
       have r₂ := eq22 x
       grind)
    | exact resolve eq15128 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15128
  have eq15153 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15143
       grind)
    | exact superpose eq15143 eq10
    | exact resolve eq10 eq15143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15143
  have eq15215 : x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15153
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15153
    | exact resolve eq15153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15153
  have eq15228 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15215
       grind)
    | exact superpose eq15215 eq16
    | exact resolve eq16 eq15215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15215
  have eq15243 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq15228
       have r₂ := eq22 x
       grind)
    | exact resolve eq15228 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15228
  have eq22437 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14292
       have i₂ := eq15243
       grind)
    | exact superpose eq15243 eq14292
    | (have r₁ := eq14292
       have r₂ := eq15243
       grind)
    | exact resolve eq14292 eq15243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14292
  have eq22438 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq22437
  have eq22471 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109 (σ y) (σ x)
       have i₂ := eq22438
       grind)
    | exact superpose eq22438 eq109
    | exact resolve eq109 eq22438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq26027 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22438
       have i₂ := eq22471
       grind)
    | exact superpose eq22471 eq22438
    | exact resolve eq22438 eq22471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22438 eq22471
  have eq26075 : (σ x) = (σ y) := by grind
  clear eq26027
  have eq26090 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26075
       grind)
    | exact superpose eq26075 eq16
    | exact resolve eq16 eq26075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26075
  have eq26176 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq26090
       have i₂ := eq114 (σ x)
       grind)
    | exact superpose eq114 eq26090
    | exact resolve eq26090 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq26090
  have eq26185 : False := by grind
  exact eq26185

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxy_pxx_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq110 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
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
  have eq115 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq110 X0 (M.op X0 x)
       have i₂ := eq110 X0 x
       grind)
    | exact superpose eq110 eq110
    | exact resolve eq110 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq146 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq148 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
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
  have eq152 : ∀ X0 X1 : G, (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 X1
       have i₂ := eq115 X1
       grind)
    | exact superpose eq115 eq148
    | (have j0 := eq148 X0 X1
       grind)
    | exact resolve eq148 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq153 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq152 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq156 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 X1
       have i₂ := eq115 (σ X1)
       grind)
    | exact superpose eq115 eq146
    | (have j0 := eq146 X0 X1
       grind)
    | exact resolve eq146 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq157 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq156 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq166 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq153 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq153
    | exact resolve eq153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq189 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq166 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq166
    | (have j0 := eq166 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq166 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq361 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq157 x y
       grind)
    | exact superpose eq157 eq16
    | (have j1 := eq157 x y
       grind)
    | exact resolve eq16 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq383 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq361
       have i₂ := eq189 x y
       grind)
    | exact superpose eq189 eq361
    | (have j1 := eq189 (σ x) (σ y)
       grind)
    | (have r₁ := eq361
       have r₂ := eq189 x y
       grind)
    | (have r₁ := eq361
       have r₂ := eq189 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq361
       have r₂ := eq189 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq361 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq361
  have eq384 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq383
  have eq387 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq384
       grind)
    | exact superpose eq384 eq16
    | exact resolve eq16 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq388 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq387
       have r₂ := eq23 x
       grind)
    | exact resolve eq387 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq387
  have eq389 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq388
       grind)
    | exact superpose eq388 eq16
    | exact resolve eq16 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq388
       grind)
    | exact superpose eq388 eq10
    | exact resolve eq10 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq405 : x = y := by
    first
    | (have i₁ := eq390
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq390
    | exact resolve eq390 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq406 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq389
       have i₂ := eq115 (σ x)
       grind)
    | exact superpose eq115 eq389
    | exact resolve eq389 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq408 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq406
       have i₂ := eq405
       grind)
    | exact superpose eq405 eq406
    | exact resolve eq406 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405 eq406
  have eq409 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq408
       have i₂ := eq115 x
       grind)
    | exact superpose eq115 eq408
    | exact resolve eq408 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq408
  have eq410 : False := by grind
  exact eq410

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pxy_x_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq31 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq46 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq51 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq46 X0
       have j1 := eq31 X0
       grind)
    | (have r₁ := eq46 X0
       have r₂ := eq31 X0
       grind)
    | exact resolve eq46 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq46
  have eq53 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq51 (τ X0)
       grind)
    | exact superpose eq51 eq18
    | exact resolve eq18 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq53
    | exact resolve eq53 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq55 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq65 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (M.op (τ X0) X1) = X1 := by
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
  have eq72 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq41 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq51 (σ X0)
       grind)
    | exact superpose eq51 eq41
    | exact resolve eq41 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq51
  have eq81 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq72
    | exact resolve eq72 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq90 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq54 (τ X0)
       grind)
    | exact superpose eq54 eq18
    | exact resolve eq18 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq90
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq139 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq64
    | exact resolve eq64 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq64 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq152 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq150 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq174 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))
       have i₂ := eq93 (τ X0)
       grind)
    | exact superpose eq93 eq18
    | exact resolve eq18 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq177 : ∀ X0 : G, (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq174
    | exact resolve eq174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq358 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq152 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq152
    | (have j0 := eq152 (τ X0)
       grind)
    | exact resolve eq152 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq358 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq358
    | (have j0 := eq358 X0
       grind)
    | exact resolve eq358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq363 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq360 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq360
    | (have j0 := eq360 X0
       grind)
    | exact resolve eq360 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq374 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq363 (τ X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq363
    | (have j0 := eq363 (τ X0)
       grind)
    | exact resolve eq363 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq493 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq65
    | exact resolve eq65 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq537 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq493 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq493
    | (have j0 := eq493 X0 X1
       grind)
    | exact resolve eq493 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq1564 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0))))))))
       have i₂ := eq177 (τ X0)
       grind)
    | exact superpose eq177 eq18
    | exact resolve eq18 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1575 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1564 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1564
    | exact resolve eq1564 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq2392 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op X0 X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq537 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2393 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op X0 X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2392 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2392
  have eq2423 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (σ (k (σ X0) (σ X0))) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq2393 (σ X0)
       grind)
    | exact superpose eq2393 eq81
    | (have j1 := eq2393 (σ X0)
       grind)
    | exact resolve eq81 eq2393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq2426 : ∀ X0 : G, (k X0 (σ (τ X0))) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq54 X0
       have i₂ := eq2393 (τ X0)
       grind)
    | exact superpose eq2393 eq54
    | (have j1 := eq2393 (τ X0)
       grind)
    | exact resolve eq54 eq2393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq2393
  have eq2435 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2426 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2426
    | (have j0 := eq2426 X0
       grind)
    | exact resolve eq2426 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2426
  have eq2438 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k (σ X0) (σ X0))) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2423 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2423
    | (have j0 := eq2423 X0
       grind)
    | exact resolve eq2423 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2423
  have eq2442 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2435 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq2435
    | (have j0 := eq2435 X0
       grind)
    | exact resolve eq2435 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2435
  have eq2445 : ∀ X0 : G, (σ (σ (k X0 X0))) = (σ (M.op (σ X0) (σ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2438 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2438
    | (have j0 := eq2438 X0
       grind)
    | exact resolve eq2438 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2438
  have eq2448 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2442 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2442
    | (have j0 := eq2442 X0
       grind)
    | exact resolve eq2442 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2442
  have eq2590 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (M.op (τ (σ X0)) (τ (σ X0)))) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2448 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq2448
    | exact resolve eq2448 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448
  have eq2665 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2590 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2590
    | (have j0 := eq2590 X0
       grind)
    | exact resolve eq2590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590
  have eq4225 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq151 X0 X0
       have i₂ := eq2665 X0
       grind)
    | exact superpose eq2665 eq151
    | (have j0 := eq151 X0 X0
       have j1 := eq2665 X0
       grind)
    | (have r₁ := eq151 X0 X0
       have r₂ := eq2665 X0
       grind)
    | exact resolve eq151 eq2665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq2665
  have eq4274 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq4225 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4225
  have eq4298 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4274 X0
       have j1 := eq152 X0
       grind)
    | (have r₁ := eq4274 X0
       have r₂ := eq152 X0
       grind)
    | exact resolve eq4274 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq4274
  have eq7367 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (τ (σ (σ (k X0 X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq2445 X0
       grind)
    | exact superpose eq2445 eq10
    | (have j1 := eq2445 X0
       grind)
    | exact resolve eq10 eq2445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2445
  have eq7425 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7367 X0
       have i₂ := eq10 (σ (k X0 X0))
       grind)
    | exact superpose eq10 eq7367
    | (have j0 := eq7367 X0
       grind)
    | exact resolve eq7367 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7367
  have eq7441 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7425 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7425
    | (have j0 := eq7425 (τ X0)
       grind)
    | exact resolve eq7425 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7425
  have eq7523 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7441 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq7441
    | (have j0 := eq7441 X0
       grind)
    | exact resolve eq7441 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7441
  have eq7534 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7523 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7523
    | (have j0 := eq7523 X0
       grind)
    | exact resolve eq7523 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7523
  have eq7537 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq7534 X0
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq7534
    | (have j0 := eq7534 X0
       grind)
    | exact resolve eq7534 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7534
  have eq7887 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq374 X0
       have i₂ := eq7537 X0
       grind)
    | exact superpose eq7537 eq374
    | (have j0 := eq374 X0
       have j1 := eq7537 X0
       grind)
    | (have r₁ := eq374 X0
       have r₂ := eq7537 X0
       grind)
    | exact resolve eq374 eq7537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374 eq7537
  have eq7932 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7887 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7887
  have eq8456 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (τ X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4298 (τ X0)
       have i₂ := eq7932 X0
       grind)
    | exact superpose eq7932 eq4298
    | (have j0 := eq4298 (τ X0)
       have j1 := eq7932 X0
       grind)
    | exact resolve eq4298 eq7932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4298 eq7932
  have eq8464 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq8456 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8456
  have eq8470 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq8464 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8464
    | (have j0 := eq8464 X0
       grind)
    | exact resolve eq8464 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8464
  have eq8481 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq8470 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq8470 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq8470 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8470
  have eq8597 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq8481 (σ X0)
       grind)
    | exact superpose eq8481 eq15
    | exact resolve eq15 eq8481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8606 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq55 X0 X0
       have i₂ := eq8481 (τ X0)
       grind)
    | exact superpose eq8481 eq55
    | exact resolve eq55 eq8481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq8649 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8606 X0
       have i₂ := eq8481 X0
       grind)
    | exact superpose eq8481 eq8606
    | exact resolve eq8606 eq8481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8606
  have eq8657 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8597 X0
       have i₂ := eq8481 X0
       grind)
    | exact superpose eq8481 eq8597
    | exact resolve eq8597 eq8481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8597
  have eq9174 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0)
       have i₂ := eq8657 X0
       grind)
    | exact superpose eq8657 eq21
    | exact resolve eq21 eq8657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34426 : ∀ X0 X1 : G, (M.op (σ X1) X0) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (M.op (σ X1) X0) = (σ (k X1 (k (τ X0) (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))) x
       have i₂ := eq1575 X0
       grind)
    | exact superpose eq1575 eq139
    | exact resolve eq139 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq1575
  have eq34519 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (M.op (σ X1) X0) = X0 ∨ (M.op (σ X1) X0) = (σ (k X1 (k (τ X0) (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq34426 X0 X1
       have i₂ := eq8657 X1
       grind)
    | exact superpose eq8657 eq34426
    | (have j0 := eq34426 X0 X1
       grind)
    | exact resolve eq34426 eq8657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34426
  have eq34636 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34519 X0 X1
       have i₂ := eq177 (τ X0)
       grind)
    | exact superpose eq177 eq34519
    | (have j0 := eq34519 X0 X1
       grind)
    | exact resolve eq34519 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq34519
  have eq34747 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34636 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq34636
    | (have j0 := eq34636 X0 X1
       grind)
    | exact resolve eq34636 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34636
  have eq34843 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq34747 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq34747 (M.op X0 (σ (M.op X1 X1))) X1
       have r₂ := eq12 X0 (σ (M.op X1 X1))
       grind)
    | (have r₁ := eq34747 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq34747 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34747
  have eq35916 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34843 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34843
    | (have j0 := eq34843 X1 (τ X0)
       grind)
    | exact resolve eq34843 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35982 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq34843 (σ X1) X0
       grind)
    | exact superpose eq34843 eq15
    | (have j1 := eq34843 (σ X1) X0
       grind)
    | exact resolve eq15 eq34843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34843
  have eq36229 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35916 X0 X1
       have i₂ := eq8649 X0
       grind)
    | exact superpose eq8649 eq35916
    | (have j0 := eq35916 X0 X1
       grind)
    | exact resolve eq35916 eq8649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8649 eq35916
  have eq36315 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36229 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq36229
    | (have j0 := eq36229 X0 X1
       grind)
    | exact resolve eq36229 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36229
  have eq36532 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq36315 X0 (τ X1)
       grind)
    | exact superpose eq36315 eq19
    | (have j1 := eq36315 X0 (τ X1)
       grind)
    | exact resolve eq19 eq36315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq36315
  have eq38350 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36532 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36532
    | exact resolve eq36532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36532
  have eq38636 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38350 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq38350
    | (have j0 := eq38350 X0 X1
       grind)
    | exact resolve eq38350 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38350
  have eq40511 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35982 x y
       grind)
    | exact superpose eq35982 eq16
    | (have j1 := eq35982 x y
       grind)
    | exact resolve eq16 eq35982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35982
  have eq41041 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40511
       have i₂ := eq38636 y x
       grind)
    | exact superpose eq38636 eq40511
    | (have j1 := eq38636 y x
       grind)
    | (have r₁ := eq40511
       have r₂ := eq38636 y x
       grind)
    | exact resolve eq40511 eq38636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38636 eq40511
  have eq41044 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq41041
  have eq41093 : x = y ∨ x = y ∨ (σ y) = (σ (k x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq537 x x
       have i₂ := eq41044
       grind)
    | exact superpose eq41044 eq537
    | exact resolve eq537 eq41044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq41044
  have eq41098 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq41093
  have eq41100 : (σ y) = (σ (M.op x x)) ∨ x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq41098
       have i₂ := eq8481 x
       grind)
    | exact superpose eq8481 eq41098
    | exact resolve eq41098 eq8481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8481 eq41098
  have eq41101 : x = y ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq41100
  have eq41328 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41101
       grind)
    | exact superpose eq41101 eq16
    | exact resolve eq16 eq41101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41101
  have eq41331 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq41328
       have r₂ := eq8657 x
       grind)
    | exact resolve eq41328 eq8657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8657 eq41328
  have eq41353 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9174 x
       have i₂ := eq41331
       grind)
    | exact superpose eq41331 eq9174
    | exact resolve eq9174 eq41331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9174
  have eq41358 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq41331
       grind)
    | exact superpose eq41331 eq10
    | exact resolve eq10 eq41331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41331
  have eq41507 : y = (M.op x x) := by
    first
    | (have i₁ := eq41358
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq41358
    | exact resolve eq41358 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41358
  have eq41777 : x = (M.op x y) := by
    first
    | (have i₁ := eq21 x
       have i₂ := eq41507
       grind)
    | exact superpose eq41507 eq21
    | exact resolve eq21 eq41507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq41507
  have eq42357 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41353
       grind)
    | exact superpose eq41353 eq16
    | exact resolve eq16 eq41353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41353
  have eq42390 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq42357
       have i₂ := eq41777
       grind)
    | exact superpose eq41777 eq42357
    | exact resolve eq42357 eq41777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41777 eq42357
  have eq42391 : False := by grind
  exact eq42391

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq68 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq68 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq68 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq13 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq68 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq68 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq121 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq126 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq116 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq116 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq116 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq127 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq121 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq121 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq121 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq121 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq134 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq126 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq126
    | (have j0 := eq126 X0 X1
       grind)
    | exact resolve eq126 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq135 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq134 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq136 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq127
    | (have j0 := eq127 X0 X1
       grind)
    | exact resolve eq127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq137 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq140 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq137 X0 X1
       have j1 := eq135 X0 X1
       grind)
    | (have r₁ := eq137 X0 X1
       have r₂ := eq135 X0 X1
       grind)
    | exact resolve eq137 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq137
  have eq152 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq140 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq140
    | exact resolve eq140 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq140 x y
       grind)
    | exact superpose eq140 eq16
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq545 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq152 X0 (τ X1)
       grind)
    | exact superpose eq152 eq18
    | exact resolve eq18 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq152
  have eq578 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq545 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq545
    | exact resolve eq545 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq596 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq578 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq578
    | exact resolve eq578 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq646 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq163
       have i₂ := eq596 x y
       grind)
    | exact superpose eq596 eq163
    | exact resolve eq163 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq596
  have eq647 : False := by grind
  exact eq647
