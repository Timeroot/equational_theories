import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,Y) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxy_y_Equation1027 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) Law1027 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a b :=
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

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then m(X,Y) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_pxy_y_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
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
  have eq151 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq114 X0
       grind)
    | exact resolve eq13 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq151 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq158 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq152 X0 (τ X1)
       grind)
    | exact superpose eq152 eq19
    | (have j1 := eq152 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq159 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq152 (σ X0) (σ X1)
       grind)
    | exact superpose eq152 eq15
    | (have j1 := eq152 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq213 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq158 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq158
    | exact resolve eq158 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq233 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq213 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq213
    | (have j0 := eq213 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq213 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq972 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq159 x y
       grind)
    | exact superpose eq159 eq16
    | (have j1 := eq159 x y
       grind)
    | exact resolve eq16 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq1000 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq972
       have i₂ := eq233 y x
       grind)
    | exact superpose eq233 eq972
    | (have j1 := eq233 (σ x) (σ y)
       grind)
    | (have r₁ := eq972
       have r₂ := eq233 y x
       grind)
    | (have r₁ := eq972
       have r₂ := eq233 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq972
       have r₂ := eq233 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq972 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq972
  have eq1001 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1000
  have eq1003 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1001
       grind)
    | exact superpose eq1001 eq16
    | exact resolve eq16 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1004 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1003
       have r₂ := eq22 x
       grind)
    | exact resolve eq1003 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1003
  have eq1005 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1004
       grind)
    | exact superpose eq1004 eq16
    | exact resolve eq16 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1006 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1004
       grind)
    | exact superpose eq1004 eq10
    | exact resolve eq10 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1047 : x = y := by
    first
    | (have i₁ := eq1006
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1006
    | exact resolve eq1006 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq1048 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq1005
       have i₂ := eq114 (σ x)
       grind)
    | exact superpose eq114 eq1005
    | exact resolve eq1005 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1051 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1048
       have i₂ := eq1047
       grind)
    | exact superpose eq1047 eq1048
    | exact resolve eq1048 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq1048
  have eq1053 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1051
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq1051
    | exact resolve eq1051 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1051
  have eq1054 : False := by grind
  exact eq1054

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_x_pxx_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
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
  have eq369 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq377 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
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
  have eq388 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq377 X0 X1
       have i₂ := eq78 X1
       grind)
    | exact superpose eq78 eq377
    | (have j0 := eq377 X0 X1
       grind)
    | exact resolve eq377 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq396 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq369 X0 X1
       have i₂ := eq78 (σ X1)
       grind)
    | exact superpose eq78 eq369
    | (have j0 := eq369 X0 X1
       grind)
    | exact resolve eq369 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq411 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq388 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq388
    | exact resolve eq388 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 (M.op (τ X0) x)
       have i₂ := eq75 (τ X0) x
       grind)
    | exact superpose eq75 eq388
    | (have j0 := eq388 X0 (M.op (τ X0) X1)
       grind)
    | exact resolve eq388 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq439 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq419 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq447 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k X0 (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq439 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq439
    | (have j0 := eq439 X0 X1
       grind)
    | exact resolve eq439 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq451 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq411 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq411
    | (have j0 := eq411 X0 X1
       grind)
    | exact resolve eq411 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq456 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (σ X0) = (k (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq447 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq447
    | exact resolve eq447 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq482 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1
       have i₂ := eq15 X0 (M.op X0 X1)
       grind)
    | exact superpose eq15 eq456
    | (have j0 := eq456 X0 X1
       grind)
    | exact resolve eq456 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq618 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X1 X0
       have i₂ := eq451 X1 X0
       grind)
    | exact superpose eq451 eq75
    | (have j1 := eq451 X1 X0
       grind)
    | exact resolve eq75 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq697 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq396 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq396
    | exact resolve eq396 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq396 x y
       grind)
    | exact superpose eq396 eq16
    | (have j1 := eq396 x y
       grind)
    | exact resolve eq16 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq728 : ∀ X0 X1 : G, (M.op (σ X1) X0) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq697 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq697
    | (have j0 := eq697 X0 X1
       grind)
    | exact resolve eq697 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq697
  have eq1520 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq728 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq728
    | exact resolve eq728 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq1641 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq482 X0 X1
       have i₂ := eq1520 X0 X1
       grind)
    | exact superpose eq1520 eq482
    | (have j1 := eq1520 X1 X0
       grind)
    | exact resolve eq482 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq1652 : ∀ X0 X1 : G, X0 = X1 ∨ (σ X0) = (σ (k X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq618 X1 X0
       have i₂ := eq1520 X0 X1
       grind)
    | exact superpose eq1520 eq618
    | (have j0 := eq618 X0 X1
       have j1 := eq1520 X1 X0
       grind)
    | exact resolve eq618 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618 eq1520
  have eq1687 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1652 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1652
  have eq1698 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1641 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641
  have eq1980 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1687 X1 X0
       have i₂ := eq1698 X1 X0
       grind)
    | exact superpose eq1698 eq1687
    | (have j0 := eq1687 (σ X0) (σ X1)
       have j1 := eq1698 (σ X0) (σ X1)
       grind)
    | exact resolve eq1687 eq1698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687 eq1698
  have eq2006 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1980 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980
  have eq2085 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq2006 (τ X0) X1
       grind)
    | exact superpose eq2006 eq18
    | (have j1 := eq2006 (τ X0) X1
       grind)
    | exact resolve eq18 eq2006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2006
  have eq2113 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (σ X1) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2085 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2085
    | (have j0 := eq2085 X0 X1
       grind)
    | exact resolve eq2085 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2085
  have eq2266 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2113 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2113
    | (have j0 := eq2113 (k (σ X0) (σ X1)) (M.op X0 X1)
       grind)
    | exact resolve eq2113 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2113
  have eq2338 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2266 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2266
    | (have j0 := eq2266 X0 X1
       grind)
    | exact resolve eq2266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266
  have eq27693 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq702
       have i₂ := eq2338 x y
       grind)
    | exact superpose eq2338 eq702
    | (have j1 := eq2338 x y
       grind)
    | (have r₁ := eq702
       have r₂ := eq2338 x y
       grind)
    | (have r₁ := eq702
       have r₂ := eq2338 (M.op x y) (k x y)
       grind)
    | (have r₁ := eq702
       have r₂ := eq2338 (k x y) (M.op x y)
       grind)
    | exact resolve eq702 eq2338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq2338
  have eq27699 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27693
  have eq27700 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq27699
  have eq27717 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27700
       grind)
    | exact superpose eq27700 eq16
    | exact resolve eq16 eq27700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27700
  have eq27718 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27717
       have i₂ := eq78 (σ x)
       grind)
    | exact superpose eq78 eq27717
    | exact resolve eq27717 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27717
  have eq27719 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27718
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq27718
    | exact resolve eq27718 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27718
  have eq27720 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq27719
  have eq27722 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq27720
       grind)
    | exact superpose eq27720 eq10
    | exact resolve eq10 eq27720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27720
  have eq27785 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27722
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq27722
    | exact resolve eq27722 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27722
  have eq27787 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27785
       grind)
    | exact superpose eq27785 eq16
    | exact resolve eq16 eq27785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27785
  have eq27788 : (σ x) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27787
       have i₂ := eq78 (σ x)
       grind)
    | exact superpose eq78 eq27787
    | exact resolve eq27787 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27787
  have eq27789 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27788
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq27788
    | exact resolve eq27788 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27788
  have eq27790 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq27789
  have eq27803 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27790
       grind)
    | exact superpose eq27790 eq16
    | exact resolve eq16 eq27790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27812 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75 (σ x) (σ y)
       have i₂ := eq27790
       grind)
    | exact superpose eq27790 eq75
    | exact resolve eq75 eq27790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq27967 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq27790
       have i₂ := eq27812
       grind)
    | exact superpose eq27812 eq27790
    | exact resolve eq27790 eq27812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27790 eq27812
  have eq28034 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq27967
       grind)
    | exact superpose eq27967 eq10
    | exact resolve eq10 eq27967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27967
  have eq28097 : x = y := by
    first
    | (have i₁ := eq28034
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28034
    | exact resolve eq28034 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28034
  have eq28101 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq27803
       have i₂ := eq28097
       grind)
    | exact superpose eq28097 eq27803
    | exact resolve eq27803 eq28097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27803 eq28097
  have eq28103 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq28101
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq28101
    | exact resolve eq28101 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq28101
  have eq28104 : False := by grind
  exact eq28104

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_x_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = a :=
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
  have eq844 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq823 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq854 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k X0 (σ (M.op (τ X0) X1))) = X0 := by
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
  have eq880 : ∀ X0 X1 : G, (τ X1) = X0 ∨ (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq854 X0 X1
       have i₂ := eq150 X0 X1
       grind)
    | exact superpose eq150 eq854
    | (have j1 := eq150 X1 X0
       grind)
    | exact resolve eq854 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq854
  have eq895 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k X1 (σ X0)) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq880 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq916 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq9101 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq895 X1 X0
       grind)
    | exact superpose eq895 eq10
    | (have j1 := eq895 X1 X0
       grind)
    | exact resolve eq10 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq9145 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9101 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq9101
    | (have j0 := eq9101 X0 X1
       grind)
    | exact resolve eq9101 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9101
  have eq9235 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq9145 (σ X0) X1
       grind)
    | exact superpose eq9145 eq37
    | (have j1 := eq9145 (σ X0) X1
       grind)
    | exact resolve eq37 eq9145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9145
  have eq9292 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9235 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq9235
    | (have j0 := eq9235 X0 X1
       grind)
    | exact resolve eq9235 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9235
  have eq9328 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9292 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9292
    | (have j0 := eq9292 X0 X1
       grind)
    | exact resolve eq9292 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9292
  have eq9345 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9328 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9328
    | (have j0 := eq9328 X0 X1
       grind)
    | exact resolve eq9328 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9328
  have eq9356 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9345 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9345
    | (have j0 := eq9345 X0 X1
       grind)
    | exact resolve eq9345 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9345
  have eq9416 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq9356 X0 (σ X1)
       grind)
    | exact superpose eq9356 eq28
    | (have j1 := eq9356 (k X0 (σ X1)) X0
       grind)
    | exact resolve eq28 eq9356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq9426 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq9356 X0 (τ X1)
       grind)
    | exact superpose eq9356 eq19
    | (have j1 := eq9356 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq9356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq9356
  have eq17536 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq9416 (σ X0) X1
       grind)
    | exact superpose eq9416 eq37
    | (have j1 := eq9416 (σ X1) X0
       grind)
    | exact resolve eq37 eq9416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq9416
  have eq17603 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17536 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq17536
    | (have j0 := eq17536 X0 X1
       grind)
    | exact resolve eq17536 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17536
  have eq17637 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17603 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17603
    | (have j0 := eq17603 X0 X1
       grind)
    | exact resolve eq17603 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17603
  have eq17650 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17637 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17637
    | (have j0 := eq17637 X0 X1
       grind)
    | exact resolve eq17637 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17637
  have eq17888 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9426 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9426
    | exact resolve eq9426 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9426
  have eq17996 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17888 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq17888
    | (have j0 := eq17888 X0 X1
       grind)
    | exact resolve eq17888 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17888
  have eq19521 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17650 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17650
    | (have j0 := eq17650 X1 (τ X0)
       grind)
    | exact resolve eq17650 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19575 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq17650 X0 X1
       grind)
    | exact superpose eq17650 eq11
    | (have j1 := eq17650 X0 X1
       grind)
    | exact resolve eq11 eq17650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17650
  have eq29081 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) ∨ (σ (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19521 X0 (τ X1)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq19521
    | (have j0 := eq19521 X1 (τ X0)
       grind)
    | exact resolve eq19521 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq19521
  have eq29227 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29081 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29081
    | (have j0 := eq29081 X0 X1
       grind)
    | exact resolve eq29081 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29081
  have eq29270 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29227 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29227
    | (have j0 := eq29227 X0 X1
       grind)
    | exact resolve eq29227 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29227
  have eq29532 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq29270 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29270
  have eq30493 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19575 x y
       grind)
    | exact superpose eq19575 eq16
    | (have j1 := eq19575 x y
       grind)
    | exact resolve eq16 eq19575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19575
  have eq30729 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq30493
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq30493
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq30493
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq30493
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq30493 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30730 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq30493
       have i₂ := eq17996 y x
       grind)
    | exact superpose eq17996 eq30493
    | (have j1 := eq17996 x (k x y)
       grind)
    | (have r₁ := eq30493
       have r₂ := eq17996 y x
       grind)
    | (have r₁ := eq30493
       have r₂ := eq17996 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq30493
       have r₂ := eq17996 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq30493 eq17996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17996 eq30493
  have eq30739 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30730
  have eq30740 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq30739
  have eq30741 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq30729
  have eq30745 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30740
       grind)
    | exact superpose eq30740 eq16
    | exact resolve eq16 eq30740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30740
  have eq30746 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq30745
       have r₂ := eq22 x
       grind)
    | exact resolve eq30745 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30745
  have eq30751 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq916
       have i₂ := eq30746
       grind)
    | exact superpose eq30746 eq916
    | exact resolve eq916 eq30746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916 eq30746
  have eq30774 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq30751
  have eq30776 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30741
       grind)
    | exact superpose eq30741 eq16
    | exact resolve eq16 eq30741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30741
  have eq30780 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30776
       have r₂ := eq22 x
       grind)
    | exact resolve eq30776 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30776
  have eq30786 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109 x y
       have i₂ := eq30780
       grind)
    | exact superpose eq30780 eq109
    | exact resolve eq109 eq30780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30780
  have eq30837 : x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq30786
  have eq30901 : (τ x) ≠ (τ x) ∨ x = y ∨ (τ x) = (τ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29532 x y
       have i₂ := eq30837
       grind)
    | exact superpose eq30837 eq29532
    | (have j0 := eq29532 x y
       grind)
    | exact resolve eq29532 eq30837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29532
  have eq30902 : x = y ∨ (τ x) = (τ (k x y)) ∨ (σ x) = (σ y) := by grind
  clear eq30901
  have eq31115 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (τ x) = (τ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30902
       grind)
    | exact superpose eq30902 eq16
    | exact resolve eq16 eq30902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30902
  have eq31121 : (σ x) = (σ y) ∨ (τ x) = (τ (k x y)) := by
    first
    | (have r₁ := eq31115
       have r₂ := eq22 x
       grind)
    | exact resolve eq31115 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31115
  have eq31124 : y = (τ (σ x)) ∨ (τ x) = (τ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq31121
       grind)
    | exact superpose eq31121 eq10
    | exact resolve eq10 eq31121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31121
  have eq31220 : x = y ∨ (τ x) = (τ (k x y)) := by
    first
    | (have i₁ := eq31124
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq31124
    | exact resolve eq31124 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31124
  have eq31227 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (τ x) = (τ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31220
       grind)
    | exact superpose eq31220 eq16
    | exact resolve eq16 eq31220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31220
  have eq31233 : (τ x) = (τ (k x y)) := by
    first
    | (have r₁ := eq31227
       have r₂ := eq22 x
       grind)
    | exact resolve eq31227 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31227
  have eq31252 : (k x y) = (σ (τ x)) := by
    first
    | (have i₁ := eq11 (k x y)
       have i₂ := eq31233
       grind)
    | exact superpose eq31233 eq11
    | exact resolve eq11 eq31233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31233
  have eq31402 : x = (k x y) := by
    first
    | (have i₁ := eq31252
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq31252
    | exact resolve eq31252 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31252
  have eq31732 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq31402
       grind)
    | exact superpose eq31402 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq31402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31402
  have eq33234 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31732
       grind)
    | exact superpose eq31732 eq16
    | exact resolve eq16 eq31732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31732
  have eq33251 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq33234
       have r₂ := eq22 x
       grind)
    | exact resolve eq33234 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq33234
  have eq33264 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109 x y
       have i₂ := eq33251
       grind)
    | exact superpose eq33251 eq109
    | exact resolve eq109 eq33251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33251
  have eq33316 : x = (M.op x y) := by grind
  clear eq33264
  have eq44790 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq30774
       have i₂ := eq30837
       grind)
    | exact superpose eq30837 eq30774
    | exact resolve eq30774 eq30837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30774 eq30837
  have eq44814 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq44790
  have eq44815 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq44814
  have eq44828 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44815
       grind)
    | exact superpose eq44815 eq16
    | exact resolve eq16 eq44815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44815
  have eq44954 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44828
       have i₂ := eq114 (σ x)
       grind)
    | exact superpose eq114 eq44828
    | exact resolve eq44828 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq44828
  have eq44966 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44954
       have i₂ := eq33316
       grind)
    | exact superpose eq33316 eq44954
    | exact resolve eq44954 eq33316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44954
  have eq44967 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq44966
  have eq45015 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44967
       grind)
    | exact superpose eq44967 eq16
    | exact resolve eq16 eq44967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45037 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109 (σ x) (σ y)
       have i₂ := eq44967
       grind)
    | exact superpose eq44967 eq109
    | exact resolve eq109 eq44967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq45159 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq45015
       have i₂ := eq33316
       grind)
    | exact superpose eq33316 eq45015
    | exact resolve eq45015 eq33316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33316 eq45015
  have eq45351 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq44967
       have i₂ := eq45037
       grind)
    | exact superpose eq45037 eq44967
    | exact resolve eq44967 eq45037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44967 eq45037
  have eq45425 : False := by grind
  exact eq45425

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pxy_pyx_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
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
  have eq143 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq114 X0
       grind)
    | exact resolve eq13 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq143 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq148 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq144 (τ X1) X0
       grind)
    | exact superpose eq144 eq19
    | (have j1 := eq144 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq149 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq144 (σ X1) (σ X0)
       grind)
    | exact superpose eq144 eq15
    | (have j1 := eq144 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq199 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq148
    | exact resolve eq148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq219 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq199
    | (have j0 := eq199 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq199 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq972 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq149 x y
       grind)
    | exact superpose eq149 eq16
    | (have j1 := eq149 x y
       grind)
    | exact resolve eq16 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq1000 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq972
       have i₂ := eq219 y x
       grind)
    | exact superpose eq219 eq972
    | (have j1 := eq219 (σ x) (σ y)
       grind)
    | (have r₁ := eq972
       have r₂ := eq219 y x
       grind)
    | (have r₁ := eq972
       have r₂ := eq219 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq972
       have r₂ := eq219 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq972 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq972
  have eq1001 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1000
  have eq1003 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1001
       grind)
    | exact superpose eq1001 eq16
    | exact resolve eq16 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1004 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1003
       have r₂ := eq22 x
       grind)
    | exact resolve eq1003 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1003
  have eq1005 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1004
       grind)
    | exact superpose eq1004 eq16
    | exact resolve eq16 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1006 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1004
       grind)
    | exact superpose eq1004 eq10
    | exact resolve eq10 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1047 : x = y := by
    first
    | (have i₁ := eq1006
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1006
    | exact resolve eq1006 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq1048 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq1005
       have i₂ := eq114 (σ x)
       grind)
    | exact superpose eq114 eq1005
    | exact resolve eq1005 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1051 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1048
       have i₂ := eq1047
       grind)
    | exact superpose eq1047 eq1048
    | exact resolve eq1048 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq1048
  have eq1053 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1051
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq1051
    | exact resolve eq1051 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1051
  have eq1054 : False := by grind
  exact eq1054

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pxy_x_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq102 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
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
  have eq544 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq519 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq519
    | exact resolve eq519 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq572 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq544 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq544
    | (have j0 := eq544 X0 X1
       grind)
    | exact resolve eq544 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq544
  have eq579 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq572 X0 X1
       have j1 := eq102 X1 X0
       grind)
    | (have r₁ := eq572 X1 X0
       have r₂ := eq102 X0 X1
       grind)
    | (have r₁ := eq572 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq102 X0 X1
       grind)
    | exact resolve eq572 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq572
  have eq587 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq579 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq579
    | exact resolve eq579 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq579 (σ X0) X1
       grind)
    | exact superpose eq579 eq15
    | (have j1 := eq579 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq627 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq587 (τ X1) X0
       grind)
    | exact superpose eq587 eq19
    | (have j1 := eq587 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq587
  have eq710 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq627 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq627
    | exact resolve eq627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq759 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq710 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq710
    | (have j0 := eq710 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq710 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq1225 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq598 x y
       grind)
    | exact superpose eq598 eq16
    | (have j1 := eq598 x y
       grind)
    | exact resolve eq16 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq1246 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1225
       have i₂ := eq759 y x
       grind)
    | exact superpose eq759 eq1225
    | (have j1 := eq759 (σ x) (σ y)
       grind)
    | (have r₁ := eq1225
       have r₂ := eq759 y x
       grind)
    | (have r₁ := eq1225
       have r₂ := eq759 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1225
       have r₂ := eq759 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1225 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759 eq1225
  have eq1247 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1246
  have eq1250 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1247
       grind)
    | exact superpose eq1247 eq16
    | exact resolve eq16 eq1247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq1251 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1250
       have r₂ := eq85 x
       grind)
    | exact resolve eq1250 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250
  have eq1252 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1251
       grind)
    | exact superpose eq1251 eq16
    | exact resolve eq16 eq1251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1253 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1251
       grind)
    | exact superpose eq1251 eq10
    | exact resolve eq10 eq1251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1300 : x = y := by
    first
    | (have i₁ := eq1253
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1253
    | exact resolve eq1253 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1301 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1252
       have i₂ := eq85 x
       grind)
    | exact superpose eq85 eq1252
    | exact resolve eq1252 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq1252
  have eq1302 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1301
       have i₂ := eq1300
       grind)
    | exact superpose eq1300 eq1301
    | exact resolve eq1301 eq1300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300 eq1301
  have eq1303 : False := by grind
  exact eq1303

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq74 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq76 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq85 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq76 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq86 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq85 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq101 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq15
    | exact resolve eq15 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq101 X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq101
    | exact resolve eq101 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq101
  have eq130 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq242 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq233 X0 X1
       have i₂ := eq112 X1
       grind)
    | exact superpose eq112 eq233
    | (have j0 := eq233 X0 X1
       grind)
    | exact resolve eq233 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq584 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq242 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq242
    | (have j0 := eq242 (M.op X1 X1) X1
       grind)
    | exact resolve eq242 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq604 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq584
    | (have j0 := eq584 (σ (M.op X1 X1)) X1
       grind)
    | exact resolve eq584 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq584
  have eq608 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq604 X0 X1
       have j1 := eq130 X1 X0
       grind)
    | (have r₁ := eq604 X0 X0
       have r₂ := eq130 X0 X1
       grind)
    | (have r₁ := eq604 (σ (M.op X0 X0)) X0
       have r₂ := eq130 X0 X1
       grind)
    | (have r₁ := eq604 (σ X0) (M.op X0 X0)
       have r₂ := eq130 X0 X1
       grind)
    | exact resolve eq604 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq604
  have eq610 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq608 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq608
    | exact resolve eq608 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq608 (σ X0) X1
       grind)
    | exact superpose eq608 eq15
    | (have j1 := eq608 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq650 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq610 (τ X1) X0
       grind)
    | exact superpose eq610 eq19
    | (have j1 := eq610 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq610
  have eq727 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq650 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq650
    | exact resolve eq650 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq772 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq727 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq727
    | (have j0 := eq727 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq727 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq1173 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq621 x y
       grind)
    | exact superpose eq621 eq16
    | (have j1 := eq621 x y
       grind)
    | exact resolve eq16 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq1188 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1173
       have i₂ := eq772 y x
       grind)
    | exact superpose eq772 eq1173
    | (have j1 := eq772 (σ x) (σ y)
       grind)
    | (have r₁ := eq1173
       have r₂ := eq772 y x
       grind)
    | (have r₁ := eq1173
       have r₂ := eq772 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1173
       have r₂ := eq772 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1173 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772 eq1173
  have eq1189 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1188
  have eq1192 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1189
       grind)
    | exact superpose eq1189 eq16
    | exact resolve eq16 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1193 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1192
       have r₂ := eq112 x
       grind)
    | exact resolve eq1192 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq1194 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1193
       grind)
    | exact superpose eq1193 eq16
    | exact resolve eq16 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1195 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1193
       grind)
    | exact superpose eq1193 eq10
    | exact resolve eq10 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq1240 : x = y := by
    first
    | (have i₁ := eq1195
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1195
    | exact resolve eq1195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1241 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1194
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq1194
    | exact resolve eq1194 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq1194
  have eq1242 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1241
       have i₂ := eq1240
       grind)
    | exact superpose eq1240 eq1241
    | exact resolve eq1241 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240 eq1241
  have eq1243 : False := by grind
  exact eq1243

/-- `Equation1052`: `x = x ◇ ((y ◇ (y ◇ z)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_pxx_pxy_Equation1052 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1052 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1052.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X1)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq62 X0 (M.op X0 X0)
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (k (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  have eq79 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq23
  have eq80 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq62 eq77
    | exact resolve eq77 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq77
  have eq326 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3502 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq326 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq326
    | (have j0 := eq326 X1 X1
       have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq326 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3506 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq3507 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) ∨ (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) ∨ (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq326 (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq326
    | (have j0 := eq326 (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq326 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3510 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq326 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq326
    | (have j0 := eq326 (σ X1) (σ X1)
       grind)
    | exact resolve eq326 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq3597 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have j0 := eq3507 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3507
  have eq3693 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69 (σ (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq3597 X0
       grind)
    | exact superpose eq3597 eq69
    | exact resolve eq69 eq3597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3722 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 X0) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3693 X0 X1
       have i₂ := eq3597 X0
       grind)
    | exact superpose eq3597 eq3693
    | exact resolve eq3693 eq3597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3597 eq3693
  have eq3774 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3722 (M.op (M.op X0 X0) (M.op X0 X0)) X1
       have i₂ := eq69 X0 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0)))
       grind)
    | exact superpose eq69 eq3722
    | exact resolve eq3722 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3722
  have eq3859 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3774 X0 X1
       have i₂ := eq69 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq69 eq3774
    | exact resolve eq3774 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3774
  have eq38103 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq3510 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3510
  have eq38104 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq38103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38103
  have eq39397 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3502 x y
       grind)
    | exact superpose eq3502 eq16
    | (have j1 := eq3502 y y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3502 x y
       grind)
    | exact resolve eq16 eq3502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39470 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq3502
  have eq39601 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq39470 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39470
  have eq39604 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq39397
  have eq39618 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39601 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq39601
    | (have j0 := eq39601 X0
       grind)
    | exact resolve eq39601 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39601
  have eq39626 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq39618
  have eq69366 : ∀ X0 : G, (σ (k (σ (τ X0)) X0)) ≠ (σ (σ (τ X0))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq38104 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq38104
    | (have j0 := eq38104 (τ X0)
       grind)
    | exact resolve eq38104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38104
  have eq69383 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq69366 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq69366
    | (have j0 := eq69366 X0
       grind)
    | exact resolve eq69366 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69366
  have eq69390 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq69383 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq69383
    | (have j0 := eq69383 X0
       grind)
    | exact resolve eq69383 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69383
  have eq69403 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq69390 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq69390
    | (have j0 := eq69390 (τ X0)
       grind)
    | exact resolve eq69390 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq69390
  have eq69420 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq69403 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq69403
    | (have j0 := eq69403 X0
       grind)
    | exact resolve eq69403 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69403
  have eq69427 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq69420 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq69420
    | (have j0 := eq69420 X0
       grind)
    | exact resolve eq69420 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69420
  have eq69438 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq69427 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq69427
    | (have j0 := eq69427 (τ X0)
       grind)
    | exact resolve eq69427 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq69446 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) ≠ (τ (M.op (M.op X0 X0) X0)) ∨ (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq69438 (M.op (M.op X0 X0) X0)
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq69438
    | (have j0 := eq69438 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq69438 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq69438
  have eq69471 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have j0 := eq69446 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69446
  have eq69990 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69 (τ (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq69471 X0
       grind)
    | exact superpose eq69471 eq69
    | exact resolve eq69 eq69471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70139 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (M.op X0 X0) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69990 X0 X1
       have i₂ := eq69471 X0
       grind)
    | exact superpose eq69471 eq69990
    | exact resolve eq69990 eq69471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69471 eq69990
  have eq335967 : (τ (M.op (σ y) (σ y))) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq79 y
       have i₂ := eq39604
       grind)
    | exact superpose eq39604 eq79
    | exact resolve eq79 eq39604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq336304 : (τ (M.op (σ y) (σ y))) = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq335967
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq335967
    | exact resolve eq335967 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335967
  have eq336388 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq39604 eq336304
    | exact resolve eq336304 eq39604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39604 eq336304
  have eq336412 : y = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq336388
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq336388
    | exact resolve eq336388 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336388
  have eq336427 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq69427 y
       grind)
    | (have r₁ := eq336412
       have r₂ := eq69427 y
       grind)
    | exact resolve eq336412 eq69427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69427 eq336412
  have eq336457 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq336427
  have eq336663 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq336457
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq336457
    | exact resolve eq336457 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336457
  have eq336696 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq336663
    | (have j1 := eq14 y y
       grind)
    | exact resolve eq336663 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336663
  have eq336715 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq336696
       have r₂ := eq16
       grind)
    | exact resolve eq336696 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336696
  have eq336720 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq69 y x
       have i₂ := eq336715
       grind)
    | exact superpose eq336715 eq69
    | exact resolve eq69 eq336715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq336752 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq3859 y x
       have i₂ := eq336715
       grind)
    | exact superpose eq336715 eq3859
    | exact resolve eq3859 eq336715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3859
  have eq336987 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq336715 eq336752
    | exact resolve eq336752 eq336715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336752
  have eq337020 : ∀ X0 : G, x = (M.op y y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq336715 eq336720
    | exact resolve eq336720 eq336715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336715 eq336720
  have eq338044 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq336987 (σ x)
       grind)
    | exact superpose eq336987 eq16
    | exact resolve eq16 eq336987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336987
  have eq338090 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq337020 eq338044
    | exact resolve eq338044 eq337020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337020 eq338044
  have eq338091 : x = (M.op y y) := by grind
  clear eq338090
  have eq367916 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq39626 eq3506
    | (have j0 := eq3506 X0
       have j1 := eq39626 X0
       grind)
    | exact resolve eq3506 eq39626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3506
  have eq367933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq39626 y
       have i₂ := eq338091
       grind)
    | exact superpose eq338091 eq39626
    | (have j0 := eq39626 y
       grind)
    | exact resolve eq39626 eq338091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39626
  have eq368359 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq367916 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367916
  have eq368452 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq367933
       have r₂ := eq16
       grind)
    | exact resolve eq367933 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367933
  have eq368615 : ∀ X0 : G, (M.op X0 (τ (M.op (σ y) (σ y)))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq70139 (σ y) X0
       have i₂ := eq368452
       grind)
    | exact superpose eq368452 eq70139
    | exact resolve eq70139 eq368452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70139
  have eq368792 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq368452 eq368615
    | exact resolve eq368615 eq368452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368452 eq368615
  have eq368927 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq368792 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq368792
    | exact resolve eq368792 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368792
  have eq369376 : x = y ∨ x = y := by
    first
    | (have i₁ := eq338091
       have i₂ := eq368927 y
       grind)
    | exact superpose eq368927 eq338091
    | exact resolve eq338091 eq368927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368927
  have eq369377 : x = y := by grind
  clear eq369376
  have eq369937 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq369377
       grind)
    | exact superpose eq369377 eq16
    | exact resolve eq16 eq369377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369938 : x = (M.op x x) := by
    first
    | (have i₁ := eq338091
       have i₂ := eq369377
       grind)
    | exact superpose eq369377 eq338091
    | exact resolve eq338091 eq369377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338091 eq369377
  have eq369963 : x = (M.op x x) := by grind
  clear eq369938
  have eq371370 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq369937
       have i₂ := eq369963
       grind)
    | exact superpose eq369963 eq369937
    | exact resolve eq369937 eq369963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369937
  have eq371473 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq368359 x
       have i₂ := eq369963
       grind)
    | exact superpose eq369963 eq368359
    | (have j0 := eq368359 x
       grind)
    | exact resolve eq368359 eq369963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368359
  have eq371580 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq371473
       have i₂ := eq369963
       grind)
    | exact superpose eq369963 eq371473
    | exact resolve eq371473 eq369963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369963 eq371473
  have eq371581 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq371580
  have eq371700 : False := by grind
  exact eq371700
