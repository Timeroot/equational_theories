import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_pxx_pxy_Equation1027 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxy_y_pxx_Equation1027 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) Law1027 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a a :=
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

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_y_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq608 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq635 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq608 X0 X1
       have i₂ := eq114 (σ X0)
       grind)
    | exact superpose eq114 eq608
    | (have j0 := eq608 X0 X1
       grind)
    | exact resolve eq608 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq894 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq635 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq635
    | exact resolve eq635 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq918 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq894 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq894
    | (have j0 := eq894 X0 X1
       grind)
    | exact resolve eq894 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq1099 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq109 X1 (σ X0)
       have i₂ := eq918 X1 X0
       grind)
    | exact superpose eq918 eq109
    | (have j1 := eq918 X1 X0
       grind)
    | exact resolve eq109 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq1140 : ∀ X0 X1 : G, (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq918 X0 X1
       have i₂ := eq1099 X1 X0
       grind)
    | exact superpose eq1099 eq918
    | (have j0 := eq918 X0 X1
       have j1 := eq1099 X1 X0
       grind)
    | exact resolve eq918 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918 eq1099
  have eq1158 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1140 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1173 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1158 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1158
    | exact resolve eq1158 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1184 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1158 (σ X1) X0
       grind)
    | exact superpose eq1158 eq15
    | (have j1 := eq1158 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1228 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq1173 X0 (τ X1)
       grind)
    | exact superpose eq1173 eq19
    | (have j1 := eq1173 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1173
  have eq1418 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1228 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1228
    | exact resolve eq1228 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1464 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1418 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1418
    | (have j0 := eq1418 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq1418 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1658 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1184 x y
       grind)
    | exact superpose eq1184 eq16
    | (have j1 := eq1184 x y
       grind)
    | exact resolve eq16 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1712 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1658
       have i₂ := eq1464 y x
       grind)
    | exact superpose eq1464 eq1658
    | (have j1 := eq1464 (σ x) (σ y)
       grind)
    | (have r₁ := eq1658
       have r₂ := eq1464 y x
       grind)
    | (have r₁ := eq1658
       have r₂ := eq1464 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1658
       have r₂ := eq1464 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1658 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464 eq1658
  have eq1715 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1712
  have eq1720 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1715
       grind)
    | exact superpose eq1715 eq16
    | exact resolve eq16 eq1715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715
  have eq1721 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1720
       have r₂ := eq22 x
       grind)
    | exact resolve eq1720 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1720
  have eq1722 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1721
       grind)
    | exact superpose eq1721 eq16
    | exact resolve eq16 eq1721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1723 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1721
       grind)
    | exact superpose eq1721 eq10
    | exact resolve eq10 eq1721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721
  have eq1770 : x = y := by
    first
    | (have i₁ := eq1723
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1723
    | exact resolve eq1723 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723
  have eq1771 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq1722
       have i₂ := eq114 (σ x)
       grind)
    | exact superpose eq114 eq1722
    | exact resolve eq1722 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722
  have eq1774 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1771
       have i₂ := eq1770
       grind)
    | exact superpose eq1770 eq1771
    | exact resolve eq1771 eq1770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770 eq1771
  have eq1776 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1774
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq1774
    | exact resolve eq1774 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1774
  have eq1777 : False := by grind
  exact eq1777

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
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
  have eq158 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq160 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = X1 := by
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
  have eq164 : ∀ X0 X1 : G, (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq160 X0 X1
       have i₂ := eq115 (τ X0)
       grind)
    | exact superpose eq115 eq160
    | (have j0 := eq160 X0 X1
       grind)
    | exact resolve eq160 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq165 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq164 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq168 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq158 X0 X1
       have i₂ := eq115 (σ X0)
       grind)
    | exact superpose eq115 eq158
    | (have j0 := eq158 X0 X1
       grind)
    | exact resolve eq158 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq169 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq178 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq165 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq165
    | exact resolve eq165 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq201 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq178
    | (have j0 := eq178 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq178 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq385 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq169 x y
       grind)
    | exact superpose eq169 eq16
    | (have j1 := eq169 x y
       grind)
    | exact resolve eq16 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq407 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq385
       have i₂ := eq201 x y
       grind)
    | exact superpose eq201 eq385
    | (have j1 := eq201 (σ x) (σ y)
       grind)
    | (have r₁ := eq385
       have r₂ := eq201 x y
       grind)
    | (have r₁ := eq385
       have r₂ := eq201 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq385
       have r₂ := eq201 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq385 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq385
  have eq408 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq407
  have eq411 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq408
       grind)
    | exact superpose eq408 eq16
    | exact resolve eq16 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq412 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq411
       have r₂ := eq23 x
       grind)
    | exact resolve eq411 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq411
  have eq413 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq412
       grind)
    | exact superpose eq412 eq16
    | exact resolve eq16 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq412
       grind)
    | exact superpose eq412 eq10
    | exact resolve eq10 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq429 : x = y := by
    first
    | (have i₁ := eq414
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq414
    | exact resolve eq414 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq430 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq413
       have i₂ := eq115 (σ x)
       grind)
    | exact superpose eq115 eq413
    | exact resolve eq413 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq432 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq430
       have i₂ := eq429
       grind)
    | exact superpose eq429 eq430
    | exact resolve eq430 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq430
  have eq433 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq432
       have i₂ := eq115 x
       grind)
    | exact superpose eq115 eq432
    | exact resolve eq432 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq432
  have eq434 : False := by grind
  exact eq434

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_x_pyy_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
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
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq102 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = X1 := by
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
       have i₂ := eq79 (τ X0)
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
       have i₂ := eq79 (σ X0)
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

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyx_pxy_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
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
  have eq8667 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = X0 ∨ (τ X0) = X1 := by
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
  have eq8707 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8667 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq8667
    | (have j0 := eq8667 X0 X1
       grind)
    | exact resolve eq8667 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8667
  have eq8794 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq8707 (σ X0) X1
       grind)
    | exact superpose eq8707 eq37
    | (have j1 := eq8707 (σ X0) X1
       grind)
    | exact resolve eq37 eq8707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8707
  have eq8851 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8794 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8794
    | (have j0 := eq8794 X0 X1
       grind)
    | exact resolve eq8794 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8794
  have eq8887 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8851 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8851
    | (have j0 := eq8851 X0 X1
       grind)
    | exact resolve eq8851 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8851
  have eq8904 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8887 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8887
    | (have j0 := eq8887 X0 X1
       grind)
    | exact resolve eq8887 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8887
  have eq8915 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8904 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8904
    | (have j0 := eq8904 X0 X1
       grind)
    | exact resolve eq8904 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8904
  have eq8972 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq8915 X0 (σ X1)
       grind)
    | exact superpose eq8915 eq28
    | (have j1 := eq8915 (k X0 (σ X1)) X0
       grind)
    | exact resolve eq28 eq8915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq8981 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq8915 X0 (τ X1)
       grind)
    | exact superpose eq8915 eq19
    | (have j1 := eq8915 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq8915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq8915
  have eq17170 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq8972 (σ X0) X1
       grind)
    | exact superpose eq8972 eq37
    | (have j1 := eq8972 (σ X1) X0
       grind)
    | exact resolve eq37 eq8972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq8972
  have eq17237 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17170 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq17170
    | (have j0 := eq17170 X0 X1
       grind)
    | exact resolve eq17170 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17170
  have eq17271 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17237 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17237
    | (have j0 := eq17237 X0 X1
       grind)
    | exact resolve eq17237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17237
  have eq17284 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17271 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17271
    | (have j0 := eq17271 X0 X1
       grind)
    | exact resolve eq17271 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17271
  have eq17524 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8981 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8981
    | exact resolve eq8981 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8981
  have eq17630 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17524 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq17524
    | (have j0 := eq17524 X0 X1
       grind)
    | exact resolve eq17524 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17524
  have eq19217 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq17284 X0 X1
       grind)
    | exact superpose eq17284 eq11
    | (have j1 := eq17284 X0 X1
       grind)
    | exact resolve eq11 eq17284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17284
  have eq20950 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19217 x y
       grind)
    | exact superpose eq19217 eq16
    | (have j1 := eq19217 x y
       grind)
    | exact resolve eq16 eq19217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19217
  have eq21546 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq20950
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq20950
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq20950
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq20950
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq20950 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21547 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq20950
       have i₂ := eq17630 y x
       grind)
    | exact superpose eq17630 eq20950
    | (have j1 := eq17630 x (k x y)
       grind)
    | (have r₁ := eq20950
       have r₂ := eq17630 y x
       grind)
    | (have r₁ := eq20950
       have r₂ := eq17630 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq20950
       have r₂ := eq17630 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq20950 eq17630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17630 eq20950
  have eq21556 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq21547
  have eq21557 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq21556
  have eq21558 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq21546
  have eq21561 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21557
       grind)
    | exact superpose eq21557 eq16
    | exact resolve eq16 eq21557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21557
  have eq21562 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq21561
       have r₂ := eq22 x
       grind)
    | exact resolve eq21561 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21561
  have eq21567 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq916
       have i₂ := eq21562
       grind)
    | exact superpose eq21562 eq916
    | exact resolve eq916 eq21562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916 eq21562
  have eq21578 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq21567
  have eq21581 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21558
       grind)
    | exact superpose eq21558 eq16
    | exact resolve eq16 eq21558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21558
  have eq21585 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21581
       have r₂ := eq22 x
       grind)
    | exact resolve eq21581 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21581
  have eq21588 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21585
       grind)
    | exact superpose eq21585 eq10
    | exact resolve eq10 eq21585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21585
  have eq21655 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21588
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21588
    | exact resolve eq21588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21588
  have eq21662 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21655
       grind)
    | exact superpose eq21655 eq16
    | exact resolve eq16 eq21655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21655
  have eq21666 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21662
       have r₂ := eq22 x
       grind)
    | exact resolve eq21662 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21662
  have eq21676 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109 x y
       have i₂ := eq21666
       grind)
    | exact superpose eq21666 eq109
    | exact resolve eq109 eq21666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21666
  have eq21721 : x = (M.op x y) := by grind
  clear eq21676
  have eq39647 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq21578
       have i₂ := eq21721
       grind)
    | exact superpose eq21721 eq21578
    | exact resolve eq21578 eq21721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21578
  have eq39666 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq39647
  have eq39677 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39666
       grind)
    | exact superpose eq39666 eq16
    | exact resolve eq16 eq39666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39666
  have eq39804 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39677
       have i₂ := eq114 (σ x)
       grind)
    | exact superpose eq114 eq39677
    | exact resolve eq39677 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq39677
  have eq39816 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39804
       have i₂ := eq21721
       grind)
    | exact superpose eq21721 eq39804
    | exact resolve eq39804 eq21721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39804
  have eq39817 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq39816
  have eq39857 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39817
       grind)
    | exact superpose eq39817 eq16
    | exact resolve eq16 eq39817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39879 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109 (σ x) (σ y)
       have i₂ := eq39817
       grind)
    | exact superpose eq39817 eq109
    | exact resolve eq109 eq39817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq39995 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq39857
       have i₂ := eq21721
       grind)
    | exact superpose eq21721 eq39857
    | exact resolve eq39857 eq21721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21721 eq39857
  have eq40159 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq39817
       have i₂ := eq39879
       grind)
    | exact superpose eq39879 eq39817
    | exact resolve eq39817 eq39879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39817 eq39879
  have eq40228 : False := by grind
  exact eq40228

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_pyx_x_pyx_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq19
  have eq35 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq69 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq75 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq31
  have eq88 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq162 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq69 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq69 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq13 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq168 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq162 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq169 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq174 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq169 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq169
    | (have j0 := eq169 X0 X1
       grind)
    | exact resolve eq169 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq175 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq174 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq599 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq175
    | exact resolve eq175 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq175 x y
       grind)
    | exact superpose eq175 eq16
    | (have j1 := eq175 x y
       grind)
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq630 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq599 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq599
    | (have j0 := eq599 X0 X1
       grind)
    | exact resolve eq599 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq599
  have eq1366 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq630 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq630
    | exact resolve eq630 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq2543 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq611
       have i₂ := eq1366 y x
       grind)
    | exact superpose eq1366 eq611
    | (have j1 := eq1366 (σ y) (σ x)
       grind)
    | exact resolve eq611 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2546 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2543
  have eq2549 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq2546
       grind)
    | exact superpose eq2546 eq35
    | exact resolve eq35 eq2546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2550 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2546
  have eq2600 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq611
       have i₂ := eq2550
       grind)
    | exact superpose eq2550 eq611
    | exact resolve eq611 eq2550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611 eq2550
  have eq2604 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2600
  have eq2666 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2604
       have i₂ := eq2549
       grind)
    | exact superpose eq2549 eq2604
    | exact resolve eq2604 eq2549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2549 eq2604
  have eq2667 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2666
  have eq2668 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2667
  have eq2921 : x = (k x (τ (σ y))) := by
    first
    | (have i₁ := eq88 x
       have i₂ := eq2668
       grind)
    | exact superpose eq2668 eq88
    | exact resolve eq88 eq2668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq2929 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 (σ x)
       have i₂ := eq2668
       grind)
    | exact superpose eq2668 eq35
    | exact resolve eq35 eq2668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2668
  have eq2944 : x = (k x y) := by
    first
    | (have i₁ := eq2921
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2921
    | exact resolve eq2921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2921
  have eq2956 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1366 y x
       have i₂ := eq2944
       grind)
    | exact superpose eq2944 eq1366
    | (have j0 := eq1366 y x
       grind)
    | exact resolve eq1366 eq2944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366 eq2944
  have eq3301 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2929
       grind)
    | exact superpose eq2929 eq16
    | exact resolve eq16 eq2929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929
  have eq3755 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3301
       have i₂ := eq2956
       grind)
    | exact superpose eq2956 eq3301
    | exact resolve eq3301 eq2956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2956
  have eq3760 : y = (M.op x x) := by grind
  clear eq3755
  have eq3763 : x = (M.op x y) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq3760
       grind)
    | exact superpose eq3760 eq35
    | exact resolve eq35 eq3760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3760
  have eq4067 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3301
       have i₂ := eq3763
       grind)
    | exact superpose eq3763 eq3301
    | exact resolve eq3301 eq3763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3301 eq3763
  have eq4072 : False := by grind
  exact eq4072

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyx_pxy_pyx_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
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
  have eq35 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq69 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq69
    | (have j0 := eq69 (σ X0) (σ X1)
       grind)
    | exact resolve eq69 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq432 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq79 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq79 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq438 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq432 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq443 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq438 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq438 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq438 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq453 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq443 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq443
    | (have j0 := eq443 X0 X1
       grind)
    | exact resolve eq443 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq454 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq453 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq778 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq454 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq454
    | (have j0 := eq454 x X0
       grind)
    | exact resolve eq454 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq785 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq454 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq454
    | exact resolve eq454 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq819 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq785 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq785
    | exact resolve eq785 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq785
  have eq853 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq778 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq778
    | (have j0 := eq778 y
       grind)
    | exact resolve eq778 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq778
  have eq860 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq853
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq853
    | exact resolve eq853 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq867 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq860
    | exact resolve eq860 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq860
  have eq1677 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq819 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq819
    | exact resolve eq819 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq1772 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1677 x y
       grind)
    | exact superpose eq1677 eq44
    | exact resolve eq44 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1677
  have eq1798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq867 eq1772
    | exact resolve eq1772 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867 eq1772
  have eq1829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1798
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1798
    | exact resolve eq1798 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1798
  have eq1836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1829
    | exact resolve eq1829 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1829
  have eq1842 : False := by grind
  exact eq1842
