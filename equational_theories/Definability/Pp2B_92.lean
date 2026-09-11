import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq42 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq42 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq42 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq43 (τ X0)
       grind)
    | exact superpose eq43 eq18
    | exact resolve eq18 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq83
    | exact resolve eq83 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq83
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq10
    | exact resolve eq10 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq169 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq205 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq9
    | exact resolve eq9 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq611 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq169
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq169
    | exact resolve eq169 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq612 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq611
       have i₂ := eq95 y
       grind)
    | exact superpose eq95 eq611
    | exact resolve eq611 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq640 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq612
       have i₂ := eq56 y x
       grind)
    | exact superpose eq56 eq612
    | (have j1 := eq56 x y
       grind)
    | exact resolve eq612 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq612
  have eq641 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq640
  have eq7791 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq641
       grind)
    | exact superpose eq641 eq10
    | exact resolve eq10 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq7844 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq7791
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq7791
    | exact resolve eq7791 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7791
  have eq7845 : (M.op x x) = (M.op y y) := by grind
  clear eq7844
  have eq7876 : ∀ X0 : G, y = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq205 X0 y
       have i₂ := eq7845
       grind)
    | exact superpose eq7845 eq205
    | exact resolve eq205 eq7845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7845
  have eq7962 : x = y := by
    first
    | (have i₁ := eq7876 x
       have i₂ := eq205 x x
       grind)
    | exact superpose eq205 eq7876
    | exact resolve eq7876 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq7876
  have eq8039 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7962
       grind)
    | exact superpose eq7962 eq16
    | exact resolve eq16 eq7962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7962
  have eq8040 : False := by grind
  exact eq8040

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pyx_pxx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
  clear eq23
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq88 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq63 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq63
    | exact resolve eq63 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       have i₂ := eq88 (M.op X0 X0)
       grind)
    | exact superpose eq88 eq9
    | exact resolve eq9 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq94 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq63 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq63 eq91
    | exact resolve eq91 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq95 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq94 X0
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq94
    | exact resolve eq94 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq102 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1 (M.op X0 (M.op X0 X0)) (M.op X0 X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq72
    | exact resolve eq72 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq95
  have eq127 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq89 X0 X0
       grind)
    | exact superpose eq89 eq89
    | exact resolve eq89 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq89 X1 X0
       grind)
    | exact superpose eq89 eq9
    | exact resolve eq9 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq89 X1 X1
       grind)
    | exact superpose eq89 eq102
    | exact resolve eq102 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq141 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq89 X0 X0
       grind)
    | exact superpose eq89 eq9
    | exact resolve eq9 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq161 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq137 X0 X0 X0
       grind)
    | exact superpose eq137 eq137
    | exact resolve eq137 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq141 (M.op X1 X0) X2 X3
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq141
    | exact resolve eq141 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq141 X2 X3 X4
       have i₂ := eq141 X2 X0 X1
       grind)
    | exact superpose eq141 eq141
    | exact resolve eq141 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq141 (M.op X0 X1) X1 X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq141
    | exact resolve eq141 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq138 X2 X3
       have i₂ := eq141 X2 X0 X1
       grind)
    | exact superpose eq141 eq138
    | exact resolve eq138 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq207 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X2
       have i₂ := eq141 X2 X0 X1
       grind)
    | exact superpose eq141 eq74
    | exact resolve eq74 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (k X0 X0)))) ∨ (σ X0) ≠ (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq66 X0 X0
       grind)
    | exact superpose eq66 eq9
    | (have j1 := eq66 X0 X0
       grind)
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq287 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq207 (M.op X2 (M.op X0 X0)) (M.op x (M.op X2 X2)) X1
       have i₂ := eq137 X2 x X0
       grind)
    | exact superpose eq137 eq207
    | exact resolve eq207 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) X0) = (M.op (M.op (M.op X1 (M.op X2 X0)) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq207 X0 X2 (M.op (M.op X1 (M.op X2 X0)) X0)
       have i₂ := eq207 (M.op X2 X0) X1 X0
       grind)
    | exact superpose eq207 eq207
    | exact resolve eq207 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq287 X1 (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) X0
       have i₂ := eq207 X1 X2 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq207 eq287
    | exact resolve eq287 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X4)) (M.op X0 X0)) = (M.op (M.op X1 (M.op (M.op X2 (M.op X3 X4)) (M.op X0 X0))) (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq206 X4 X3 (M.op (M.op X2 (M.op X3 X4)) (M.op X0 X0)) X1
       have i₂ := eq9 X0 (M.op X3 X4) X2
       grind)
    | exact superpose eq9 eq206
    | exact resolve eq206 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq141 (M.op X1 (M.op (M.op X2 X1) X0)) X0 x
       have i₂ := eq206 X1 X2 X0 x
       grind)
    | exact superpose eq206 eq141
    | exact resolve eq141 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0) = (M.op (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq207 (M.op X3 X0) X2 (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0)
       have i₂ := eq206 (M.op X2 (M.op X3 X0)) X1 X0 X3
       grind)
    | exact superpose eq206 eq207
    | exact resolve eq207 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq476 X0 X1 X2
       have i₂ := eq63 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq63 eq476
    | exact resolve eq476 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq499 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) X0) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq488 X0 X1 X2
       have i₂ := eq201 (M.op (M.op X2 X1) X0) X1
       grind)
    | exact superpose eq201 eq488
    | exact resolve eq488 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq488
  have eq501 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq499 X0 X1 X2
       have i₂ := eq206 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq206 eq499
    | exact resolve eq499 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq502 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq300 X0 X1 X2
       have i₂ := eq501 X0 (M.op X2 X0) X1
       grind)
    | exact superpose eq501 eq300
    | exact resolve eq300 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq503 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq478 X0 X1 X2 X3
       have i₂ := eq501 X0 (M.op X2 (M.op X3 X0)) X1
       grind)
    | exact superpose eq501 eq478
    | exact resolve eq478 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq504 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq386 X0 X1 X2
       have i₂ := eq501 (M.op X0 (M.op X1 X1)) X1 X2
       grind)
    | exact superpose eq501 eq386
    | exact resolve eq386 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq505 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq504 X0 X1 X2
       have i₂ := eq63 X0 (M.op X1 X1)
       grind)
    | exact superpose eq63 eq504
    | exact resolve eq504 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq585 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq501 X1 (M.op x (M.op X0 X0)) (M.op x (M.op x x))
       have i₂ := eq137 x x X0
       grind)
    | exact superpose eq137 eq501
    | exact resolve eq501 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq501 (M.op X1 (M.op X0 X0)) (M.op X1 X1) x
       have i₂ := eq137 X1 x X0
       grind)
    | exact superpose eq137 eq501
    | exact resolve eq501 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq630 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq593 X0 X1
       have i₂ := eq63 X1 (M.op X0 X0)
       grind)
    | exact superpose eq63 eq593
    | exact resolve eq593 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq643 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq505 X0 X1 X2
       have i₂ := eq630 X1 X0
       grind)
    | exact superpose eq630 eq505
    | exact resolve eq505 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505 eq630
  have eq780 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq503 (M.op X1 X0) X2 X0 (M.op x (M.op X1 X1))
       have i₂ := eq287 X1 X0 x
       grind)
    | exact superpose eq287 eq503
    | exact resolve eq503 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq826 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq780 X0 X1 X2
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq780
    | exact resolve eq780 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq780
  have eq857 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X2 (M.op X1 (M.op X0 X0)))) = (M.op X0 (M.op X2 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq826 (M.op X1 (M.op X0 X0)) X2 (M.op x (M.op X1 X1))
       have i₂ := eq137 X1 x X0
       grind)
    | exact superpose eq137 eq826
    | exact resolve eq826 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq938 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq80 X0 X0
       grind)
    | exact superpose eq80 eq9
    | (have j1 := eq80 X0 X0
       grind)
    | exact resolve eq9 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq966 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq951 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq972 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (k X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq966 X0 X1 X2
       have j1 := eq268 X0 X1 X2
       grind)
    | (have r₁ := eq966 X0 X1 X2
       have r₂ := eq268 X0 X1 X2
       grind)
    | exact resolve eq966 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq966
  have eq995 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 (M.op (M.op X2 X1) (k (σ (τ X0)) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq972 (τ X0) X1 X2
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq972
    | exact resolve eq972 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1005 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq502 (σ (k X0 X0)) x (M.op x x)
       have i₂ := eq972 X0 x x
       grind)
    | exact superpose eq972 eq502
    | exact resolve eq502 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq1033 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq995 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq995
    | exact resolve eq995 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq1070 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq207 x x (k X0 X0)
       have i₂ := eq1033 X0 x x
       grind)
    | exact superpose eq1033 eq207
    | exact resolve eq207 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq1120 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq585 (k X0 X0) X0
       have i₂ := eq1070 X0
       grind)
    | exact superpose eq1070 eq585
    | exact resolve eq585 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1133 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1070 X0
       have i₂ := eq1120 X0
       grind)
    | exact superpose eq1120 eq1070
    | exact resolve eq1070 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070 eq1120
  have eq1157 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1005 X0
       have i₂ := eq1133 X0
       grind)
    | exact superpose eq1133 eq1005
    | exact resolve eq1005 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1227 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1133 (σ X0)
       grind)
    | exact superpose eq1133 eq15
    | exact resolve eq15 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1229 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq1133 (τ X0)
       grind)
    | exact superpose eq1133 eq32
    | exact resolve eq32 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1236 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1229 X0
       have i₂ := eq1133 X0
       grind)
    | exact superpose eq1133 eq1229
    | exact resolve eq1229 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1238 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1227 X0
       have i₂ := eq1133 X0
       grind)
    | exact superpose eq1133 eq1227
    | exact resolve eq1227 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133 eq1227
  have eq1273 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1157 X0
       have i₂ := eq1238 (M.op X0 X0)
       grind)
    | exact superpose eq1238 eq1157
    | exact resolve eq1157 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1275 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq938
       have i₂ := eq1238 x
       grind)
    | exact superpose eq1238 eq938
    | exact resolve eq938 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq1280 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1273 X0
       have i₂ := eq826 X0 X0 X0
       grind)
    | exact superpose eq826 eq1273
    | exact resolve eq1273 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq1299 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (M.op X1 (τ (M.op X0 X0))) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq287 (τ X0) (τ X0) x
       have i₂ := eq1236 X0
       grind)
    | exact superpose eq1236 eq287
    | exact resolve eq287 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1311 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1299 X0 x
       have i₂ := eq585 x (τ (M.op X0 X0))
       grind)
    | exact superpose eq585 eq1299
    | exact resolve eq1299 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq1313 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1311 X0
       have i₂ := eq1236 (M.op X0 X0)
       grind)
    | exact superpose eq1236 eq1311
    | exact resolve eq1311 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236 eq1311
  have eq1314 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1313 X0
       have i₂ := eq826 X0 X0 X0
       grind)
    | exact superpose eq826 eq1313
    | exact resolve eq1313 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826 eq1313
  have eq1730 : ∀ X0 X1 X2 : G, (τ X2) = (M.op (τ X2) (τ (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1314 X2
       have i₂ := eq141 X2 X0 X1
       grind)
    | exact superpose eq141 eq1314
    | exact resolve eq1314 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq3450 : ∀ X0 X1 X2 : G, (M.op X0 (τ (M.op X1 (M.op (M.op X2 X1) (σ X0))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1730 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1730
    | exact resolve eq1730 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq3620 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (τ (M.op X2 (M.op (M.op X3 X2) (σ X0)))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq141 X1 (τ (M.op X2 (M.op (M.op X3 X2) (σ X0)))) X0
       have i₂ := eq3450 X0 X2 X3
       grind)
    | exact superpose eq3450 eq141
    | exact resolve eq141 eq3450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3624 : ∀ X0 X1 X2 X3 : G, (τ (M.op X1 (M.op (M.op X2 X1) (σ X0)))) = (M.op (τ (M.op X1 (M.op (M.op X2 X1) (σ X0)))) (M.op (M.op X3 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq287 X0 (τ (M.op X1 (M.op (M.op X2 X1) (σ X0)))) X3
       have i₂ := eq3450 X0 X1 X2
       grind)
    | exact superpose eq3450 eq287
    | exact resolve eq287 eq3450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq3660 : ∀ X0 X1 X2 : G, (τ (M.op X1 (M.op (M.op X2 X1) (σ X0)))) = (M.op (τ (M.op X1 (M.op (M.op X2 X1) (σ X0)))) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3624 X0 X1 X2 x
       have i₂ := eq502 X0 x X0
       grind)
    | exact superpose eq502 eq3624
    | exact resolve eq3624 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq3624
  have eq3676 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (τ (M.op X1 (M.op (M.op X2 X1) (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3660 X0 X1 X2
       have i₂ := eq3620 X0 X0 X1 X2
       grind)
    | exact superpose eq3620 eq3660
    | exact resolve eq3660 eq3620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3620 eq3660
  have eq4216 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq76 X2 X2 X3 X4
       have i₂ := eq141 X2 X0 X1
       grind)
    | exact superpose eq141 eq76
    | exact resolve eq76 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4229 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq76 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq76 eq76
    | exact resolve eq76 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4296 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq190 X0 X1 X2 X3
       have i₂ := eq4229 X0 X1 X0
       grind)
    | exact superpose eq4229 eq190
    | exact resolve eq190 eq4229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq4300 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op X0 X0)))) = (M.op (M.op X0 X0) (M.op X2 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq857 X0 X1 X2
       have i₂ := eq4229 X2 X1 (M.op X0 X0)
       grind)
    | exact superpose eq4229 eq857
    | exact resolve eq857 eq4229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq5698 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq141 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) X1 x
       have i₂ := eq161 X1 x X0
       grind)
    | exact superpose eq161 eq141
    | exact resolve eq141 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5748 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) = (M.op (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq127 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op X2 X1)
       have i₂ := eq161 X1 X2 X0
       grind)
    | exact superpose eq161 eq127
    | exact resolve eq127 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq5778 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) = (M.op (M.op X1 (M.op (M.op X2 X1) (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5748 X0 X1 X2
       have i₂ := eq4229 (M.op X2 X1) X2 X1
       grind)
    | exact superpose eq4229 eq5748
    | exact resolve eq5748 eq4229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5748
  have eq5819 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X0) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5698 X0 X1
       have i₂ := eq4229 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op X1 (M.op X1 X1)) (M.op X0 X0)
       grind)
    | exact superpose eq4229 eq5698
    | exact resolve eq5698 eq4229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5698
  have eq5883 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) = (M.op (M.op X1 (M.op X1 (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5778 X0 X1 X2
       have i₂ := eq4296 X1 X2 X1 X2
       grind)
    | exact superpose eq4296 eq5778
    | exact resolve eq5778 eq4296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5778
  have eq5919 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5819 X0 X1
       have i₂ := eq4296 (M.op X0 X0) (M.op X1 (M.op X1 X1)) (M.op X0 X0) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq4296 eq5819
    | exact resolve eq5819 eq4296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5819
  have eq5962 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) = (M.op (M.op X1 (M.op X1 (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5883 X0 X1 X2
       have i₂ := eq4229 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op X1 (M.op X1 X1)) (M.op X0 X0)
       grind)
    | exact superpose eq4229 eq5883
    | exact resolve eq5883 eq4229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5883
  have eq5968 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5919 X0 X1
       have i₂ := eq4300 X0 (M.op X1 (M.op X1 X1)) (M.op X0 X0)
       grind)
    | exact superpose eq4300 eq5919
    | exact resolve eq5919 eq4300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5919
  have eq5991 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 (M.op X2 X1))) X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5962 X0 X1 X2
       have i₂ := eq4296 (M.op X0 X0) (M.op X1 (M.op X1 X1)) (M.op X0 X0) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq4296 eq5962
    | exact resolve eq5962 eq4296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4296 eq5962
  have eq5994 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5968 X0 X1
       have i₂ := eq643 (M.op X1 (M.op X1 X1)) X0 X0
       grind)
    | exact superpose eq643 eq5968
    | exact resolve eq5968 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5968
  have eq6017 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 (M.op X2 X1))) X0) = (M.op X0 (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5991 X0 X1 X2
       have i₂ := eq4300 X0 (M.op X1 (M.op X1 X1)) (M.op X0 X0)
       grind)
    | exact superpose eq4300 eq5991
    | exact resolve eq5991 eq4300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4300 eq5991
  have eq6027 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 (M.op X2 X1))) X0) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6017 X0 X1 X2
       have i₂ := eq643 (M.op X1 (M.op X1 X1)) X0 X0
       grind)
    | exact superpose eq643 eq6017
    | exact resolve eq6017 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6017
  have eq6030 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 (M.op X1 (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6027 X0 X1 X2
       have i₂ := eq5994 X0 X1
       grind)
    | exact superpose eq5994 eq6027
    | exact resolve eq6027 eq5994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5994 eq6027
  have eq6197 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6030 X2 (M.op X1 X0) (M.op X1 (M.op X1 X1))
       have i₂ := eq127 X0 X1
       grind)
    | exact superpose eq127 eq6030
    | exact resolve eq6030 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq6229 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) X3) = (M.op (M.op (M.op (M.op X1 X2) X0) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6030 X3 (M.op (M.op X1 X2) X0) X2
       have i₂ := eq206 X2 X1 X0 (M.op X1 X2)
       grind)
    | exact superpose eq206 eq6030
    | exact resolve eq6030 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq6367 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X0 (M.op X0 (M.op X2 X0)))) (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X0 (M.op X0 (M.op X2 X0))) X1
       have i₂ := eq6030 (M.op (M.op X1 (M.op X0 (M.op X0 (M.op X2 X0)))) (M.op X3 X3)) X0 X2
       grind)
    | exact superpose eq6030 eq9
    | exact resolve eq9 eq6030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6030
  have eq6433 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X3) = (M.op (M.op (M.op X1 X2) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6229 X0 X1 X2 X3
       have i₂ := eq585 (M.op X1 X2) X0
       grind)
    | exact superpose eq585 eq6229
    | exact resolve eq6229 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585 eq6229
  have eq6454 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op X1 X0) (M.op X0 (M.op X0 (M.op X0 X0)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6197 X0 X1 X2
       have i₂ := eq643 X0 X0 X1
       grind)
    | exact superpose eq643 eq6197
    | exact resolve eq6197 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq6197
  have eq6513 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op X1 X0) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6454 X0 X1 X2
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq6454
    | exact resolve eq6454 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq6454
  have eq6570 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6513 X0 X1 X2
       have i₂ := eq6433 X0 X1 X0 X2
       grind)
    | exact superpose eq6433 eq6513
    | exact resolve eq6513 eq6433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6433 eq6513
  have eq6712 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6570 X1 X0 X2
       have i₂ := eq6570 X1 X3 X2
       grind)
    | (have i₁ := eq6570 X0 X1 X2
       have i₂ := eq6570 X0 X0 X2
       grind)
    | exact superpose eq6570 eq6570
    | exact resolve eq6570 eq6570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6570
  have eq7247 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X4) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X0 X0))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6712 X1 (M.op (M.op X2 X3) (M.op X0 X0)) X4 X3
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq6712
    | exact resolve eq6712 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7682 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X4)) (M.op X0 X0)) = (M.op X0 (M.op X4 X0)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq462 X0 x X2 X3 X4
       have i₂ := eq7247 X0 x X2 (M.op X3 X4) (M.op X4 X0)
       grind)
    | exact superpose eq7247 eq462
    | exact resolve eq462 eq7247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq7247
  have eq7736 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq6367 X0 x X2 X3
       have i₂ := eq7682 X3 x X0 (M.op X0 (M.op X2 X0))
       grind)
    | exact superpose eq7682 eq6367
    | exact resolve eq6367 eq7682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6367 eq7682
  have eq8727 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op (M.op (M.op X1 X2) (M.op X3 (M.op X1 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq76 X0 (M.op (M.op X1 X2) (M.op X3 (M.op X1 X2))) X2 X1
       have i₂ := eq7736 (M.op X1 X2) X3 X0
       grind)
    | exact superpose eq7736 eq76
    | exact resolve eq76 eq7736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq7736
  have eq8764 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op (M.op X2 (M.op X3 (M.op X1 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8727 X0 X1 X2 X3
       have i₂ := eq4229 X3 X1 X2
       grind)
    | exact superpose eq4229 eq8727
    | exact resolve eq8727 eq4229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4229 eq8727
  have eq11369 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6712 X2 (M.op X3 (M.op X4 X0)) X1 X0
       have i₂ := eq8764 X1 X4 X0 X3
       grind)
    | exact superpose eq8764 eq6712
    | exact resolve eq6712 eq8764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6712 eq8764
  have eq44316 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1275
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1275
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq1275 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq44318 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq44316
  have eq59985 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) X2)) = (τ (M.op X0 (M.op (M.op X1 X0) (σ X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq141 X2 X3 X4
       have i₂ := eq3676 X2 X0 X1
       grind)
    | exact superpose eq3676 eq141
    | exact resolve eq141 eq3676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq3676
  have eq103875 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq4216 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq192 (M.op X4 X5) X3 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) X0 X1
       grind)
    | (have i₁ := eq4216 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq192 X0 X1 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) (M.op X4 X5) X3
       grind)
    | exact superpose eq192 eq4216
    | exact resolve eq4216 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq4216
  have eq105096 : ∀ X0 X1 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op X5 X6)))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq103875 X0 X1 x x x X5 X6
       have i₂ := eq11369 X5 X6 x x x
       grind)
    | exact superpose eq11369 eq103875
    | exact resolve eq103875 eq11369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11369 eq103875
  have eq106568 : ∀ X0 X1 X2 X3 : G, (σ (M.op X3 X3)) = (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 (σ X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1238 X3
       have i₂ := eq105096 X1 X2 X0 (σ X3)
       grind)
    | exact superpose eq105096 eq1238
    | exact resolve eq1238 eq105096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq742313 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (τ (M.op X0 (M.op (M.op X1 X0) (σ (M.op X2 X3)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq105096 x x X2 X3
       have i₂ := eq59985 X0 X1 (M.op X2 X3) x x
       grind)
    | exact superpose eq59985 eq105096
    | exact resolve eq105096 eq59985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59985 eq105096
  have eq871393 : ∀ X0 X1 : G, (σ (M.op x x)) = (M.op (σ y) (M.op X0 (M.op (M.op X1 X0) (σ y)))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq106568 (σ y) X0 X1 x
       have i₂ := eq44318
       grind)
    | exact superpose eq44318 eq106568
    | exact resolve eq106568 eq44318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44318 eq106568
  have eq871839 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq871393 x x
       have i₂ := eq207 x x (σ y)
       grind)
    | exact superpose eq207 eq871393
    | exact resolve eq871393 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq871393
  have eq871840 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq871839
  have eq872019 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq871840
       grind)
    | exact superpose eq871840 eq10
    | exact resolve eq10 eq871840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871840
  have eq872439 : y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq872019
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq872019
    | exact resolve eq872019 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872019
  have eq872440 : y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq872439
  have eq872939 : ∀ X0 X1 : G, (M.op x x) = (M.op y (τ (M.op X0 (M.op (M.op X1 X0) (σ y))))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq742313 X0 X1 y x
       have i₂ := eq872440
       grind)
    | exact superpose eq872440 eq742313
    | exact resolve eq742313 eq872440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742313 eq872440
  have eq872948 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq872939 x x
       have i₂ := eq3450 y x x
       grind)
    | exact superpose eq3450 eq872939
    | exact resolve eq872939 eq3450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3450 eq872939
  have eq872949 : y = (M.op x x) := by grind
  clear eq872948
  have eq873034 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1280 x
       have i₂ := eq872949
       grind)
    | exact superpose eq872949 eq1280
    | exact resolve eq1280 eq872949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280 eq872949
  have eq896184 : False := by grind
  exact eq896184

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq88 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq326 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq311 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq327 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq326 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq335 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq327 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq327 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq327 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq344 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq335 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq335
    | (have j0 := eq335 X0 X1
       grind)
    | exact resolve eq335 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq345 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq344 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq350 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq345 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq345
    | exact resolve eq345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq345 x y
       grind)
    | exact superpose eq345 eq16
    | exact resolve eq16 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq457 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq350 X0 (τ X1)
       grind)
    | exact superpose eq350 eq17
    | exact resolve eq17 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq350
  have eq472 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq457 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq457
    | exact resolve eq457 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq481 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq472 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq472
    | exact resolve eq472 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq500 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq361
       have i₂ := eq481 x y
       grind)
    | exact superpose eq481 eq361
    | exact resolve eq361 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq481
  have eq501 : False := by grind
  exact eq501

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_x_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq40 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq40
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq40 X0 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq40 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq40
    | exact resolve eq40 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 (M.op X0 (M.op X0 X0)) X0
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X0 X0)) X0
       have r₂ := eq66 X0
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq73 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq86 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq86 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq86
    | (have j0 := eq86 (σ X0)
       grind)
    | exact resolve eq86 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq22
    | (have j1 := eq86 (σ X0)
       grind)
    | exact resolve eq22 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq103 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq102
    | (have j0 := eq102 X0
       grind)
    | exact resolve eq102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq107 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq144 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq155 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq72
    | exact resolve eq72 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq72 X1 X0
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq72 X1 X1
       grind)
    | exact superpose eq72 eq107
    | exact resolve eq107 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq243 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq171 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq171
    | exact resolve eq171 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq320 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X2
       have i₂ := eq173 X2 X0 X1
       grind)
    | exact superpose eq173 eq66
    | exact resolve eq66 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq321 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X2
       have i₂ := eq173 X2 X0 X1
       grind)
    | exact superpose eq173 eq71
    | exact resolve eq71 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq325 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq178 X2 X3
       have i₂ := eq173 X2 X0 X1
       grind)
    | exact superpose eq173 eq178
    | exact resolve eq178 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq171 X2 X3 X2
       have i₂ := eq173 X2 X0 X1
       grind)
    | exact superpose eq173 eq171
    | exact resolve eq171 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq173 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq173 eq9
    | exact resolve eq9 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq320 x x (M.op X0 X0)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq320
    | exact resolve eq320 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq384 X0
       grind)
    | exact superpose eq384 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq384 X0
       grind)
    | exact resolve eq12 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq417 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq406 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq435 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq417 (σ X0)
       grind)
    | exact superpose eq417 eq28
    | exact resolve eq28 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq436 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq417 (τ X0)
       grind)
    | exact superpose eq417 eq17
    | exact resolve eq17 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq437 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq436 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq436
    | exact resolve eq436 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq438 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq435 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq435
    | exact resolve eq435 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq727 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (M.op (σ X0) (σ X1)) (M.op X2 X2))) = X2 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq144 X0 X1
       grind)
    | (have i₁ := eq9 X0 (σ X1) (σ X0)
       have i₂ := eq144 X0 X1
       grind)
    | exact superpose eq144 eq9
    | (have j1 := eq144 X0 X1
       grind)
    | exact resolve eq9 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq144 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq144 X0 X1
       grind)
    | exact superpose eq144 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq144 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq144 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq144 X0 X1
       grind)
    | exact resolve eq13 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq144 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq755 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq743 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq756 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq755 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq761 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq756 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq756
    | (have j0 := eq756 X0 X1
       grind)
    | exact resolve eq756 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq1048 : ∀ X0 X1 : G, (k (σ X1) (k X0 (σ (τ X0)))) = (σ (k X1 (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 (τ X0) X1
       have i₂ := eq86 (τ X0)
       grind)
    | exact superpose eq86 eq20
    | (have j1 := eq86 (τ X0)
       grind)
    | exact resolve eq20 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq86
  have eq1078 : ∀ X0 X1 : G, (σ (k X1 (M.op (τ X0) (τ X0)))) = (k (σ X1) (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1048 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1048
    | (have j0 := eq1048 X0 X1
       grind)
    | exact resolve eq1048 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1281 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) (M.op X0 X1))) = (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1))) X3 X4
       have i₂ := eq69 X1 X0 (M.op X1 (M.op X0 X1)) X2
       grind)
    | exact superpose eq69 eq69
    | exact resolve eq69 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1282 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 X2 X2 X3 X4
       have i₂ := eq173 X2 X0 X1
       grind)
    | exact superpose eq173 eq69
    | exact resolve eq69 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1283 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X0 (M.op X1 X0) X2 X3
       have i₂ := eq173 X0 X0 X1
       grind)
    | exact superpose eq173 eq69
    | exact resolve eq69 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1294 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq69 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq69 eq69
    | exact resolve eq69 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1354 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1283 X0 X1 x x
       have i₂ := eq69 X0 X0 x x
       grind)
    | exact superpose eq69 eq1283
    | exact resolve eq1283 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1741 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq9
    | (have j1 := eq95 X0
       grind)
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1888 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op (M.op X3 (M.op X3 X3)) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq155 X2 X3
       have i₂ := eq173 X2 X0 X1
       grind)
    | exact superpose eq173 eq155
    | exact resolve eq155 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq173
  have eq2775 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op (M.op X4 X0) (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq243 (M.op X1 (M.op (M.op X2 X1) X0)) X3 (M.op X4 X0)
       have i₂ := eq325 X1 X2 X0 X4
       grind)
    | exact superpose eq325 eq243
    | exact resolve eq243 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2981 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2775 X0 X1 X2 X3 X4
       have i₂ := eq40 X4 X0
       grind)
    | exact superpose eq40 eq2775
    | exact resolve eq2775 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2775
  have eq3043 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2981 X0 X1 X2 X3 X4
       have i₂ := eq40 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq40 eq2981
    | exact resolve eq2981 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2981
  have eq3071 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3043 X0 X1 X2 X3 X4
       have i₂ := eq325 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq325 eq3043
    | exact resolve eq3043 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3043
  have eq3080 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq3071 X0 x x X3 X4
       have i₂ := eq321 x x X0
       grind)
    | exact superpose eq321 eq3071
    | exact resolve eq3071 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321 eq3071
  have eq3110 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3080 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq243 X0 x X1
       grind)
    | exact superpose eq243 eq3080
    | exact resolve eq3080 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3201 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3110 X0 X1 X2
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq3110
    | exact resolve eq3110 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3110
  have eq3223 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3201 X0 X1 X2
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq3201
    | exact resolve eq3201 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3201
  have eq3271 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) ∨ (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1)))
       have i₂ := eq69 X1 X0 (M.op X1 (M.op X0 X1)) X2
       grind)
    | exact superpose eq69 eq68
    | (have j0 := eq68 (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1)))
       grind)
    | exact resolve eq68 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq69
  have eq3286 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) ∨ (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3271 X0 X1 X2
       have i₂ := eq1354 (M.op X1 (M.op X0 X1)) X2
       grind)
    | exact superpose eq1354 eq3271
    | (have j0 := eq3271 X0 X1 X2
       grind)
    | exact resolve eq3271 eq1354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3271
  have eq3307 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) ∨ (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3286 X0 X1 X2
       have i₂ := eq40 X1 (M.op X0 X1)
       grind)
    | exact superpose eq40 eq3286
    | (have j0 := eq3286 X0 X1 X2
       grind)
    | exact resolve eq3286 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3286
  have eq3310 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1)))) ∨ (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3307 X0 X1 X1
       have i₂ := eq1354 (M.op X1 (M.op X0 X1)) X1
       grind)
    | exact superpose eq1354 eq3307
    | (have j0 := eq3307 X0 X1 x
       grind)
    | exact resolve eq3307 eq1354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3307
  have eq3313 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) ∨ (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3310 X0 X0
       have i₂ := eq40 X0 (M.op X0 X0)
       grind)
    | exact superpose eq40 eq3310
    | (have j0 := eq3310 X0 X1
       grind)
    | exact resolve eq3310 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3310
  have eq5125 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X0)) X0) (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq326 X0 X3 (M.op (M.op X2 (M.op X3 X0)) X0) X1
       have i₂ := eq320 (M.op X3 X0) X2 X0
       grind)
    | exact superpose eq320 eq326
    | exact resolve eq326 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq5298 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5125 X0 X1 X2 X3
       have i₂ := eq40 (M.op X2 (M.op X3 X0)) X0
       grind)
    | exact superpose eq40 eq5125
    | exact resolve eq5125 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5125
  have eq5374 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X3 X0)) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq5298 X0 x X2 X3
       have i₂ := eq3080 X0 x (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq3080 eq5298
    | exact resolve eq5298 eq3080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3080 eq5298
  have eq6239 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 X1 X1 X0
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq336
    | exact resolve eq336 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6244 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq336 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq171 X1 x X0
       grind)
    | exact superpose eq171 eq336
    | exact resolve eq336 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq6254 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq336 X3 X2 (M.op X1 (M.op X2 X3)) (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq9 eq336
    | exact resolve eq336 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq6408 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op X0 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6254 X0 X1 X2 X3
       have i₂ := eq3223 X0 X3 X0
       grind)
    | exact superpose eq3223 eq6254
    | exact resolve eq6254 eq3223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6254
  have eq6415 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6244 X0 X1
       have i₂ := eq3223 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq3223 eq6244
    | exact resolve eq6244 eq3223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6244
  have eq6709 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6415 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq243 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq243 eq6415
    | exact resolve eq6415 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq6772 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (M.op X1 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6239 X1 (M.op X0 X0)
       have i₂ := eq6415 X1 X0
       grind)
    | exact superpose eq6415 eq6239
    | exact resolve eq6239 eq6415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6929 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6709 X0 X1
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq6709
    | exact resolve eq6709 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6709
  have eq6984 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6929 X0 X1
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq6929
    | exact resolve eq6929 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq6929
  have eq7111 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6984 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq325 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq325 eq6984
    | exact resolve eq6984 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq7118 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6415 (M.op X0 (M.op X1 X0)) X1
       have i₂ := eq6984 X0 X1
       grind)
    | exact superpose eq6984 eq6415
    | exact resolve eq6415 eq6984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7167 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq320 (M.op X0 (M.op X2 X0)) (M.op X2 X2) X1
       have i₂ := eq6984 X0 X2
       grind)
    | exact superpose eq6984 eq320
    | exact resolve eq320 eq6984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7231 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7118 X0 X1
       have i₂ := eq40 X0 (M.op X1 X0)
       grind)
    | exact superpose eq40 eq7118
    | exact resolve eq7118 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7118
  have eq7293 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7231 X0 X1
       have i₂ := eq5374 X0 X0 X1
       grind)
    | exact superpose eq5374 eq7231
    | exact resolve eq7231 eq5374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5374 eq7231
  have eq7395 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7111 X2 X1 X0
       have i₂ := eq7111 X2 X1 X3
       grind)
    | (have i₁ := eq7111 X0 X1 X2
       have i₂ := eq7111 X0 X1 X1
       grind)
    | exact superpose eq7111 eq7111
    | exact resolve eq7111 eq7111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7405 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7111 (M.op X0 (M.op X2 X0)) X2 X1
       have i₂ := eq6984 X0 X2
       grind)
    | exact superpose eq6984 eq7111
    | exact resolve eq7111 eq6984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6984 eq7111
  have eq10255 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7167 X2 X3 X1
       have i₂ := eq7395 X2 (M.op X1 X2) (M.op X2 X3) X0
       grind)
    | (have i₁ := eq7167 X2 X3 X1
       have i₂ := eq7395 X0 (M.op X1 X2) (M.op X2 X3) X2
       grind)
    | exact superpose eq7395 eq7167
    | exact resolve eq7167 eq7395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7167
  have eq10951 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (σ X1)) (M.op X2 X2))) = X2 ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq727 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq727
    | exact resolve eq727 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq11124 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (σ X1)) (M.op X2 X2))) = X2 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10951 X0 X1 X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq10951
    | (have j0 := eq10951 X0 X1 X2
       grind)
    | exact resolve eq10951 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq10951
  have eq27740 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op (M.op (M.op X2 (M.op X3 X1)) (M.op X2 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6772 (M.op X2 (M.op X3 X1)) X0
       have i₂ := eq6408 X0 X2 X3 X1
       grind)
    | exact superpose eq6408 eq6772
    | exact resolve eq6772 eq6408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6408 eq6772
  have eq28280 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op (M.op (M.op X3 X1) (M.op X2 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27740 X0 X1 X2 X3
       have i₂ := eq40 X2 (M.op X3 X1)
       grind)
    | exact superpose eq40 eq27740
    | exact resolve eq27740 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27740
  have eq28444 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op (M.op X1 (M.op X2 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28280 X0 X1 X2 X3
       have i₂ := eq1294 X2 X3 X1
       grind)
    | exact superpose eq1294 eq28280
    | exact resolve eq28280 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28280
  have eq28515 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28444 X0 X1 X2 X3
       have i₂ := eq6239 X0 X1
       grind)
    | exact superpose eq6239 eq28444
    | exact resolve eq28444 eq6239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6239 eq28444
  have eq28768 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq28515 X4 X3 X1 X2
       have i₂ := eq7395 X3 (M.op X1 (M.op X2 X3)) X4 X0
       grind)
    | (have i₁ := eq28515 X4 X3 X1 X2
       have i₂ := eq7395 X0 (M.op X1 (M.op X2 X3)) X4 X3
       grind)
    | exact superpose eq7395 eq28515
    | exact resolve eq28515 eq7395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7395 eq28515
  have eq36450 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7293 X0 X1
       have i₂ := eq1294 X0 X1 X0
       grind)
    | exact superpose eq1294 eq7293
    | exact resolve eq7293 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7293
  have eq36557 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 (M.op (M.op X2 X1) (k (σ (τ X0)) X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1741 (τ X0) X1 X2
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1741
    | (have j0 := eq1741 (τ X0) X1 X2
       grind)
    | exact resolve eq1741 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1741
  have eq36844 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36557 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36557
    | (have j0 := eq36557 X0 X1 X2
       grind)
    | exact resolve eq36557 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36557
  have eq36903 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36844 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36844
    | (have j0 := eq36844 X0 X1 X2
       grind)
    | exact resolve eq36844 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36844
  have eq41969 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) = (k (σ (M.op (M.op (τ X0) (τ X0)) (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1078 X0 (M.op (M.op (τ X0) (τ X0)) (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))
       have i₂ := eq74 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq74 eq1078
    | (have j0 := eq1078 X0 x
       grind)
    | exact resolve eq1078 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1078
  have eq42064 : ∀ X0 : G, (σ (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) = (k (σ (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq41969 X0
       have i₂ := eq6415 (M.op (τ X0) (τ X0)) (τ X0)
       grind)
    | exact superpose eq6415 eq41969
    | (have j0 := eq41969 X0
       grind)
    | exact resolve eq41969 eq6415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6415 eq41969
  have eq42071 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq42064 X0
       have i₂ := eq9 (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq9 eq42064
    | (have j0 := eq42064 X0
       grind)
    | exact resolve eq42064 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42064
  have eq42075 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq42071 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq42071
    | (have j0 := eq42071 X0
       grind)
    | exact resolve eq42071 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42071
  have eq42087 : ∀ X0 : G, (k X0 (σ (τ X0))) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq437 X0
       have i₂ := eq42075 X0
       grind)
    | exact superpose eq42075 eq437
    | (have j1 := eq42075 X0
       grind)
    | exact resolve eq437 eq42075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq42075
  have eq42285 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq42087 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq42087
    | (have j0 := eq42087 X0
       grind)
    | exact resolve eq42087 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42087
  have eq45302 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) (M.op X0 X1))) = (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq1281 X0 X1 x X3 X4
       have i₂ := eq1354 (M.op X1 (M.op X0 X1)) x
       grind)
    | exact superpose eq1354 eq1281
    | exact resolve eq1281 eq1354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281
  have eq45303 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq45302 X0 X1 X3 X4
       have i₂ := eq40 X1 (M.op X0 X1)
       grind)
    | exact superpose eq40 eq45302
    | exact resolve eq45302 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq45302
  have eq45304 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) (M.op X0 X1))) = (M.op X1 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq45303 X0 X1 X3 X4
       have i₂ := eq1294 X1 X0 X1
       grind)
    | exact superpose eq1294 eq45303
    | exact resolve eq45303 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45303
  have eq45952 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq36450 X3 X2
       have i₂ := eq45304 X2 X3 X0 X1
       grind)
    | exact superpose eq45304 eq36450
    | exact resolve eq36450 eq45304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65439 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ X0) (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11124 X1 X0 (M.op X1 (σ X0))
       have i₂ := eq1294 (M.op X1 (σ X0)) X1 (σ X0)
       grind)
    | exact superpose eq1294 eq11124
    | (have j0 := eq11124 X1 X0 x
       grind)
    | exact resolve eq11124 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11124
  have eq65872 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ X0) (M.op (σ X0) (M.op X1 (σ X0))))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65439 X0 X1
       have i₂ := eq45304 X1 (σ X0) (σ X0) X1
       grind)
    | exact superpose eq45304 eq65439
    | (have j0 := eq65439 X0 X1
       grind)
    | exact resolve eq65439 eq45304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65439
  have eq65962 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65872 X0 X1
       have i₂ := eq36450 (σ X0) X1
       grind)
    | exact superpose eq36450 eq65872
    | (have j0 := eq65872 X0 X1
       grind)
    | exact resolve eq65872 eq36450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36450 eq65872
  have eq74726 : ∀ X0 X1 X2 X3 : G, (k X3 (τ (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 (σ X3))))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq438 X3
       have i₂ := eq45952 X1 X2 X0 (σ X3)
       grind)
    | exact superpose eq45952 eq438
    | exact resolve eq438 eq45952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq45952
  have eq93061 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X0) X0) = (M.op X1 (M.op (M.op X2 X1) (M.op (M.op X3 (k X0 X0)) (k X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq45304 (M.op X3 (k X0 X0)) (k X0 X0) X1 X2
       have i₂ := eq36903 X0 (k X0 X0) X3
       grind)
    | exact superpose eq36903 eq45304
    | (have j1 := eq36903 X0 X1 X2
       grind)
    | exact resolve eq45304 eq36903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36903 eq45304
  have eq93372 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) X0) = (M.op X1 (M.op (M.op X2 X1) (M.op (k X0 X0) (k X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93061 X0 X1 X2 x
       have i₂ := eq1354 (k X0 X0) x
       grind)
    | exact superpose eq1354 eq93061
    | (have j0 := eq93061 X0 X1 X2 x
       grind)
    | exact resolve eq93061 eq1354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354 eq93061
  have eq93484 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq93372 X0 x x
       have i₂ := eq9 (k X0 X0) x x
       grind)
    | exact superpose eq9 eq93372
    | (have j0 := eq93372 X0 x x
       grind)
    | exact resolve eq93372 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93372
  have eq93537 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (k X0 X0) X1))) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq320 X0 (k X0 X0) X1
       have i₂ := eq93484 X0
       grind)
    | exact superpose eq93484 eq320
    | (have j1 := eq93484 X0
       grind)
    | exact resolve eq320 eq93484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93484
  have eq128952 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 X5) = (M.op X4 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1282 (M.op X2 (M.op X3 X4)) X1 X5 X4 X3
       have i₂ := eq1888 (M.op X3 X4) X2 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X5) X0
       grind)
    | exact superpose eq1888 eq1282
    | exact resolve eq1282 eq1888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282 eq1888
  have eq129887 : ∀ X0 X4 X5 : G, (M.op X5 X5) = (M.op X4 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X4 X5)))) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq128952 X0 x x x X4 X5
       have i₂ := eq28768 x x x X4 X5
       grind)
    | exact superpose eq28768 eq128952
    | exact resolve eq128952 eq28768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128952
  have eq171170 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = (k (M.op X1 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X1 (M.op X0 X1)))) ∨ (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3313 X1 X0
       have i₂ := eq1294 X0 X1 X0
       grind)
    | exact superpose eq1294 eq3313
    | (have j0 := eq3313 X0 X1
       grind)
    | exact resolve eq3313 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3313
  have eq171171 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X1 (M.op X0 X1))) ∨ (M.op X1 (M.op X1 (M.op X0 X1))) = (k (M.op X1 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq171170 X0 X1
       have i₂ := eq1294 X1 X0 X1
       grind)
    | exact superpose eq1294 eq171170
    | (have j0 := eq171170 X0 X1
       grind)
    | exact resolve eq171170 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294 eq171170
  have eq171473 : ∀ X0 : G, (M.op (k X0 X0) X0) ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq171171 (k X0 X0) X0
       have i₂ := eq93537 X0 X0
       grind)
    | exact superpose eq93537 eq171171
    | (have j1 := eq93537 X0 x
       grind)
    | exact resolve eq171171 eq93537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93537 eq171171
  have eq171538 : ∀ X0 : G, (M.op (k X0 X0) X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq171473 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq171473 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq171473 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171473
  have eq172397 : ∀ X0 : G, (σ X0) ≠ (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq171538 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq171538
    | exact resolve eq171538 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217256 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X3) = (M.op X4 (M.op (M.op X2 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X2))))) (M.op X2 (M.op X4 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq129887 X2 X4 X3
       have i₂ := eq129887 X1 X0 X2
       grind)
    | exact superpose eq129887 eq129887
    | exact resolve eq129887 eq129887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129887
  have eq220217 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X3) = (M.op X4 (M.op (M.op X1 (M.op X0 X2)) (M.op X2 (M.op X4 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq217256 X0 X1 X2 X3 X4
       have i₂ := eq28768 X2 X0 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X2)) (M.op X2 (M.op X4 X3))
       grind)
    | exact superpose eq28768 eq217256
    | exact resolve eq217256 eq28768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28768 eq217256
  have eq906324 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq753 X0 X1
       have i₂ := eq65962 X0 (σ X1)
       grind)
    | (have i₁ := eq753 X0 X0
       have i₂ := eq65962 X0 X1
       grind)
    | exact superpose eq65962 eq753
    | (have j0 := eq753 X0 X1
       have j1 := eq65962 X0 (σ X1)
       grind)
    | exact resolve eq753 eq65962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753 eq65962
  have eq906511 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq906324 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906324
  have eq906682 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq906511 X0 X1
       have j1 := eq761 X0 X1
       grind)
    | (have r₁ := eq906511 X1 X1
       have r₂ := eq761 X1 X1
       grind)
    | (have r₁ := eq906511 X0 X1
       have r₂ := eq761 X0 X1
       grind)
    | exact resolve eq906511 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761 eq906511
  have eq906984 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq906682 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq906682
    | (have j0 := eq906682 X0 X1
       grind)
    | exact resolve eq906682 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906682
  have eq906985 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq906984 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906984
  have eq1021246 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq906985 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq906985
    | exact resolve eq906985 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1021598 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq906985 x y
       grind)
    | exact superpose eq906985 eq16
    | (have j1 := eq906985 x y
       grind)
    | exact resolve eq16 eq906985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1022246 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq906985 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1022355 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1021246 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1021246
    | (have j0 := eq1021246 X0 X1
       grind)
    | exact resolve eq1021246 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1021246
  have eq1023198 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1022246 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1022246
    | (have j0 := eq1022246 (τ X1) (τ X0)
       grind)
    | exact resolve eq1022246 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1023408 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1023198 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1023198
    | (have j0 := eq1023198 X0 X1
       grind)
    | exact resolve eq1023198 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023198
  have eq1023493 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1023408 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1023408
    | (have j0 := eq1023408 X0 X1
       grind)
    | exact resolve eq1023408 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023408
  have eq1023538 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1023493 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1023493
    | (have j0 := eq1023493 X0 X1
       grind)
    | exact resolve eq1023493 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023493
  have eq1023573 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1023538 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1023538
    | (have j0 := eq1023538 X0 X1
       grind)
    | exact resolve eq1023538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023538
  have eq1025664 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1022355 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1022355
    | exact resolve eq1022355 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022355
  have eq1027461 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq42285 X0
       have i₂ := eq1025664 X0 (k X0 X0)
       grind)
    | exact superpose eq1025664 eq42285
    | (have j0 := eq42285 X0
       have j1 := eq1025664 X0 (k X0 X0)
       grind)
    | exact resolve eq42285 eq1025664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42285
  have eq1028141 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1027461 X0
       have j1 := eq171538 X0
       grind)
    | (have r₁ := eq1027461 X0
       have r₂ := eq171538 X0
       grind)
    | exact resolve eq1027461 eq171538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171538 eq1027461
  have eq1028442 : ∀ X0 X1 : G, (M.op (M.op X1 (k X0 X0)) (M.op X0 (k X0 X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7405 X0 X1 (k X0 X0)
       have i₂ := eq1028141 X0
       grind)
    | exact superpose eq1028141 eq7405
    | (have j1 := eq1028141 X0
       grind)
    | exact resolve eq7405 eq1028141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1029035 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1028442 X0 x
       have i₂ := eq3223 (k X0 X0) X0 x
       grind)
    | exact superpose eq3223 eq1028442
    | (have j0 := eq1028442 X0 x
       grind)
    | exact resolve eq1028442 eq3223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3223 eq1028442
  have eq1110648 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1021598
       have i₂ := eq1025664 y x
       grind)
    | exact superpose eq1025664 eq1021598
    | (have j1 := eq1025664 (σ y) (σ x)
       grind)
    | exact resolve eq1021598 eq1025664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021598
  have eq1110658 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1110648
  have eq1110666 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1110658
       grind)
    | exact superpose eq1110658 eq16
    | exact resolve eq16 eq1110658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110696 : ∀ X0 X1 : G, y = (k y (τ (M.op (σ x) (M.op X0 (M.op (M.op X1 X0) (σ x)))))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq74726 (σ x) X0 X1 y
       have i₂ := eq1110658
       grind)
    | exact superpose eq1110658 eq74726
    | exact resolve eq74726 eq1110658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74726
  have eq1111031 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op X0 (M.op X1 X2)) (M.op X2 (σ x)))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq220217 X1 X0 X2 (σ y) (σ x)
       have i₂ := eq1110658
       grind)
    | exact superpose eq1110658 eq220217
    | exact resolve eq220217 eq1110658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110658
  have eq1111073 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1111031 x x x
       have i₂ := eq10255 x x x (σ x)
       grind)
    | exact superpose eq10255 eq1111031
    | exact resolve eq1111031 eq10255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111031
  have eq1111199 : y = (k y (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1110696 x x
       have i₂ := eq320 x x (σ x)
       grind)
    | exact superpose eq320 eq1110696
    | exact resolve eq1110696 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320 eq1110696
  have eq1111252 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1111199
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1111199
    | exact resolve eq1111199 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111199
  have eq1111266 : y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1111252
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1111252 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111252
  have eq1111267 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1111266
       have i₂ := eq1025664 y x
       grind)
    | exact superpose eq1025664 eq1111266
    | (have j1 := eq1025664 y x
       grind)
    | exact resolve eq1111266 eq1025664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025664
  have eq1111327 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1022246 x y
       have i₂ := eq1111266
       grind)
    | exact superpose eq1111266 eq1022246
    | (have j0 := eq1022246 x y
       grind)
    | exact resolve eq1022246 eq1111266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022246
  have eq1111328 : x ≠ y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1023573 y x
       have i₂ := eq1111266
       grind)
    | exact superpose eq1111266 eq1023573
    | (have j0 := eq1023573 y x
       grind)
    | exact resolve eq1023573 eq1111266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023573
  have eq1113063 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1110666
       have i₂ := eq1111267
       grind)
    | exact superpose eq1111267 eq1110666
    | exact resolve eq1110666 eq1111267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110666 eq1111267
  have eq1113064 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1113063
       have r₂ := eq1111328
       grind)
    | exact resolve eq1113063 eq1111328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113063
  have eq1116117 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq103 y
       have i₂ := eq1111073
       grind)
    | exact superpose eq1111073 eq103
    | exact resolve eq103 eq1111073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq1111073
  have eq1117064 : (k y y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1116117
       have r₂ := eq1113064
       grind)
    | exact resolve eq1116117 eq1113064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113064 eq1116117
  have eq1117141 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1117064
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1117064
    | exact resolve eq1117064 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117064
  have eq1117335 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1028141 y
       have i₂ := eq1117141
       grind)
    | exact superpose eq1117141 eq1028141
    | exact resolve eq1028141 eq1117141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028141 eq1117141
  have eq1117454 : x = (M.op x y) ∨ x = y := by grind
  clear eq1117335
  have eq1117482 : x = (M.op x y) := by
    first
    | (have r₁ := eq1117454
       have r₂ := eq1111328
       grind)
    | exact resolve eq1117454 eq1111328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111328 eq1117454
  have eq1117630 : ∀ X0 : G, (M.op x (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq7405 X0 x y
       have i₂ := eq1117482
       grind)
    | exact superpose eq1117482 eq7405
    | exact resolve eq7405 eq1117482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7405
  have eq1117864 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op x (M.op (M.op X0 (M.op X1 X2)) (M.op X2 x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq220217 X1 X0 X2 y x
       have i₂ := eq1117482
       grind)
    | exact superpose eq1117482 eq220217
    | exact resolve eq220217 eq1117482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220217
  have eq1117901 : x = (M.op y y) := by
    first
    | (have i₁ := eq1117864 x x x
       have i₂ := eq10255 x x x x
       grind)
    | exact superpose eq10255 eq1117864
    | exact resolve eq1117864 eq10255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10255 eq1117864
  have eq1118322 : x ≠ x ∨ x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1117901
       grind)
    | exact superpose eq1117901 eq13
    | exact resolve eq13 eq1117901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117901
  have eq1118681 : x = (k y y) ∨ x = y := by grind
  clear eq1118322
  have eq1147059 : (M.op x y) = (k y y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq1117630 (k y y)
       have i₂ := eq1029035 y
       grind)
    | exact superpose eq1029035 eq1117630
    | (have j1 := eq1029035 y
       grind)
    | exact resolve eq1117630 eq1029035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029035 eq1117630
  have eq1147930 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1147059
       have i₂ := eq1117482
       grind)
    | exact superpose eq1117482 eq1147059
    | exact resolve eq1147059 eq1117482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147059
  have eq1207062 : x ≠ y ∨ x = (k y y) := by grind
  clear eq1147930
  have eq1207129 : x = (k y y) := by
    first
    | (have r₁ := eq1207062
       have r₂ := eq1118681
       grind)
    | exact resolve eq1207062 eq1118681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118681 eq1207062
  have eq1207481 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq172397 y
       have i₂ := eq1207129
       grind)
    | exact superpose eq1207129 eq172397
    | exact resolve eq172397 eq1207129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172397 eq1207129
  have eq1814357 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1207481
       have i₂ := eq906985 x y
       grind)
    | exact superpose eq906985 eq1207481
    | (have j1 := eq906985 x y
       grind)
    | exact resolve eq1207481 eq906985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906985 eq1207481
  have eq1814358 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1814357
       have r₂ := eq1111327
       grind)
    | exact resolve eq1814357 eq1111327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111327 eq1814357
  have eq1814365 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1814358
       have i₂ := eq1111266
       grind)
    | exact superpose eq1111266 eq1814358
    | exact resolve eq1814358 eq1111266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111266 eq1814358
  have eq1814366 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1814365
  have eq1814394 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1814366
       grind)
    | exact superpose eq1814366 eq16
    | exact resolve eq16 eq1814366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814366
  have eq1815032 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1814394
       have i₂ := eq1117482
       grind)
    | exact superpose eq1117482 eq1814394
    | exact resolve eq1814394 eq1117482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117482 eq1814394
  have eq1815033 : False := by grind
  exact eq1815033

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq24 eq35
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq63 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq22 eq36
  have eq80 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq73
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq73 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88
    | exact resolve eq88 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq747 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq97 eq67
    | (have j0 := eq67 (σ y) (σ x)
       grind)
    | exact resolve eq67 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq748 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq747
    | exact resolve eq747 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq751 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq748
       have r₂ := eq27
       grind)
    | exact resolve eq748 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq756 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq751 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq751
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq751
       grind)
    | exact resolve eq13 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq758 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq756
  have eq764 : (τ (σ y)) = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq758 eq57
    | exact resolve eq57 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq758
  have eq766 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq764
    | exact resolve eq764 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq764
  have eq782 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq67 x y
       have i₂ := eq766
       grind)
    | exact superpose eq766 eq67
    | (have j0 := eq67 y x
       grind)
    | exact resolve eq67 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq783 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq782
  have eq785 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq783
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq783
    | exact resolve eq783 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq810 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq785
       grind)
    | exact superpose eq785 eq53
    | exact resolve eq53 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq811 : y ≠ y ∨ x = (M.op x y) ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq785
       grind)
    | exact superpose eq785 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq785
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq785
       grind)
    | exact resolve eq12 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq815 : x = (M.op x y) ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq811
  have eq816 : x = (M.op x y) ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq815
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq815
    | exact resolve eq815 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq817 : (k y x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq816
  have eq818 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq810
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq810
    | exact resolve eq810 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq810
  have eq868 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq817
       grind)
    | exact superpose eq817 eq73
    | exact resolve eq73 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq996 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq868
       have i₂ := eq818
       grind)
    | exact superpose eq818 eq868
    | exact resolve eq868 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818 eq868
  have eq1010 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq996
  have eq1012 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1010
    | exact resolve eq1010 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1014 : (τ (σ (M.op x y))) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1012 eq80
    | exact resolve eq80 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1012
  have eq1017 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq1014
    | exact resolve eq1014 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1014
  have eq1020 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq1017
       have r₂ := eq63
       grind)
    | exact resolve eq1017 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1017
  have eq1026 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq1020
       grind)
    | exact superpose eq1020 eq73
    | exact resolve eq73 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1020
  have eq1028 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq1026
    | exact resolve eq1026 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1026
  have eq1031 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1028 eq67
    | (have j0 := eq67 (σ y) (σ x)
       grind)
    | exact resolve eq67 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1032 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1031
    | exact resolve eq1031 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1035 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1032
       have r₂ := eq27
       grind)
    | exact resolve eq1032 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1039 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1035 eq53
    | exact resolve eq53 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1040 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1035 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1035
       grind)
    | exact resolve eq12 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1044 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq1040
  have eq1045 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq1044
    | exact resolve eq1044 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1046 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq1039
    | exact resolve eq1039 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1039
  have eq1047 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1028 eq1045
    | exact resolve eq1045 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1542 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1046 eq1047
    | exact resolve eq1047 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046 eq1047
  have eq1543 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1542
       have r₂ := eq27
       grind)
    | exact resolve eq1542 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq1544 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1543 eq27
    | exact resolve eq27 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1546 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1543 eq64
    | (have r₁ := eq64
       have r₂ := eq1543
       grind)
    | exact resolve eq64 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq1543
  have eq1565 : (σ x) = (k (σ y) (σ x)) := by grind
  clear eq1546
  have eq1573 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1028 eq1565
    | exact resolve eq1565 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028 eq1565
  have eq1583 : False := by grind
  exact eq1583

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pyy_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq74 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq77 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq82
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82
    | exact resolve eq82 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq101 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq101
  have eq134 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
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
  have eq479 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq892 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq75 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq908 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq920 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq892 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq922 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq920 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq920 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq920 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq920 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq932 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq922 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq922
    | (have j0 := eq922 X0 X1
       grind)
    | exact resolve eq922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq1587 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq537 X0 X0 X0
       grind)
    | exact superpose eq537 eq50
    | exact resolve eq50 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1588 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq537 X0 X0 X0
       grind)
    | exact superpose eq537 eq51
    | exact resolve eq51 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq1753 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq479 X0
       have i₂ := eq1587 X0
       grind)
    | exact superpose eq1587 eq479
    | exact resolve eq479 eq1587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq1781 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1587 eq483
    | exact resolve eq483 eq1587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1587
  have eq1793 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq483 eq1781
    | exact resolve eq1781 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781
  have eq1828 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq50 eq1753
    | exact resolve eq1753 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1753
  have eq1990 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1588 eq483
    | exact resolve eq483 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588
  have eq2002 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq483 eq1990
    | exact resolve eq1990 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq1990
  have eq6580 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq77 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq77
    | (have j0 := eq77 y
       grind)
    | exact resolve eq77 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq6607 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6580
  have eq6614 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6607
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq6607
    | exact resolve eq6607 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq6607
  have eq6625 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6614
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6614 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6614
  have eq6632 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6625 eq106
    | exact resolve eq106 eq6625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq6701 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq135
    | (have j0 := eq135 (M.op x y)
       grind)
    | exact resolve eq135 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq6727 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6701
  have eq6733 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq134 eq6727
    | exact resolve eq6727 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq6727
  have eq6746 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6733
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6733 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6733
  have eq11544 : (σ y) ≠ (k (σ y) (σ (M.op x y))) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq74 eq932
    | (have j0 := eq932 y (M.op x y)
       grind)
    | exact resolve eq932 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq932
  have eq11569 : (σ y) ≠ (k (σ y) (σ (M.op x y))) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq11544
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11544
    | exact resolve eq11544 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11544
  have eq11632 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq11569
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11569
    | exact resolve eq11569 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11569
  have eq11695 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq11632
    | exact resolve eq11632 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11632
  have eq11753 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq11695
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11695
    | exact resolve eq11695 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11695
  have eq11807 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq11753
    | exact resolve eq11753 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11753
  have eq16802 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16803 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq16802
    | exact resolve eq16802 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16802
  have eq16808 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq16803
       have r₂ := eq27
       grind)
    | exact resolve eq16803 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16803
  have eq16810 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq16808
    | exact resolve eq16808 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16808
  have eq16813 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16810 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq16810
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq16810
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16810
       grind)
    | exact resolve eq13 eq16810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16816 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16810 eq53
    | exact resolve eq53 eq16810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16810
  have eq16847 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq16813
  have eq16858 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq16816
    | exact resolve eq16816 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16816
  have eq17375 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16847 eq93
    | exact resolve eq93 eq16847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq16847
  have eq17385 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17375
  have eq17390 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17385 eq16858
    | exact resolve eq16858 eq17385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16858 eq17385
  have eq17467 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq17390
  have eq17477 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17467
       have r₂ := eq27
       grind)
    | exact resolve eq17467 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17467
  have eq17481 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq17477
       grind)
    | exact superpose eq17477 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq17477
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq17477
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq17477
       grind)
    | exact resolve eq12 eq17477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17482 : y ≠ y ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq17477
       grind)
    | exact superpose eq17477 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq17477
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq17477
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq17477
       grind)
    | exact resolve eq13 eq17477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17485 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq17477
       grind)
    | exact superpose eq17477 eq53
    | exact resolve eq53 eq17477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq17477
  have eq17516 : (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17482
  have eq17517 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17481
  have eq17530 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17485
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17485
    | exact resolve eq17485 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17485
  have eq17531 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17517
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17517
    | exact resolve eq17517 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17517
  have eq17532 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17531
  have eq17539 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17532
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17532
    | exact resolve eq17532 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17532
  have eq17543 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6625 eq107
    | exact resolve eq107 eq6625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq6625
  have eq17644 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq17539
       grind)
    | exact superpose eq17539 eq72
    | exact resolve eq72 eq17539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq17539
  have eq17671 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17644
    | exact resolve eq17644 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17644
  have eq17848 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq17516
       grind)
    | exact superpose eq17516 eq44
    | exact resolve eq44 eq17516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq17516
  have eq18691 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17848
       have i₂ := eq17530
       grind)
    | exact superpose eq17530 eq17848
    | exact resolve eq17848 eq17530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17530 eq17848
  have eq18741 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18691
  have eq18747 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq18741
    | exact resolve eq18741 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18741
  have eq18760 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18747 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq18747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18747
  have eq18763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18760
    | exact resolve eq18760 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18760
  have eq18768 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq18763
       have r₂ := eq27
       grind)
    | exact resolve eq18763 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18763
  have eq18770 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18768
    | exact resolve eq18768 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18768
  have eq18771 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18770
  have eq18839 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18771 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq18771
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq18771
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq18771
       grind)
    | exact resolve eq12 eq18771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18771
  have eq18875 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18839
  have eq18886 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18875
    | exact resolve eq18875 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18875
  have eq18887 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq18886
  have eq18892 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18887
    | exact resolve eq18887 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18887
  have eq18997 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18892 eq17671
    | exact resolve eq17671 eq18892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17671 eq18892
  have eq19007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18997
  have eq19009 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19007
       have r₂ := eq27
       grind)
    | exact resolve eq19007 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19007
  have eq19013 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19009 eq51
    | exact resolve eq51 eq19009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq19045 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19009 eq2002
    | exact resolve eq2002 eq19009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq19056 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19045
    | exact resolve eq19045 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19045
  have eq19810 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19056 eq19013
    | exact resolve eq19013 eq19056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19013 eq19056
  have eq19858 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq19810
  have eq19889 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19009 eq19858
    | exact resolve eq19858 eq19009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19009 eq19858
  have eq19928 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq19889
  have eq20035 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq19928 eq52
    | exact resolve eq52 eq19928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq19928
  have eq20084 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20035 x x
       have i₂ := eq568 sF3 (M.op x x)
       grind)
    | exact superpose eq568 eq20035
    | exact resolve eq20035 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq20035
  have eq20099 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20084 eq6632
    | exact resolve eq6632 eq20084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20084
  have eq20197 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq20099
    | exact resolve eq20099 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq20099
  have eq20387 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq20197
       grind)
    | exact superpose eq20197 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq20197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20388 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq20387
  have eq82382 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq20388
       grind)
    | exact superpose eq20388 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq20388
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20388
       grind)
    | exact resolve eq13 eq20388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82447 : x ≠ y ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq20388
  have eq82451 : y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq82382
  have eq97468 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20197
       have i₂ := eq82451
       grind)
    | exact superpose eq82451 eq20197
    | exact resolve eq20197 eq82451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20197 eq82451
  have eq97493 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq97468
  have eq97511 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq97493
       have r₂ := eq82447
       grind)
    | exact resolve eq97493 eq82447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82447 eq97493
  have eq97596 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1828 y
       have i₂ := eq97511
       grind)
    | exact superpose eq97511 eq1828
    | exact resolve eq1828 eq97511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97511
  have eq97729 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq97596
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97596
    | exact resolve eq97596 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97596
  have eq97730 : x = (M.op x y) := by grind
  clear eq97729
  have eq97758 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq97730 eq20
    | exact resolve eq20 eq97730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq97853 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq97730 eq1793
    | exact resolve eq1793 eq97730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793
  have eq97927 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq97853
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97853
    | exact resolve eq97853 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq97853
  have eq97982 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq97758
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq97758
    | exact resolve eq97758 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97758
  have eq97986 : x = (M.op y y) := by
    first
    | exact superpose eq97730 eq97927
    | exact resolve eq97927 eq97730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97927
  have eq98006 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq97982 eq26
    | exact resolve eq26 eq97982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq98354 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq17543
       have i₂ := eq97986
       grind)
    | exact superpose eq97986 eq17543
    | exact resolve eq17543 eq97986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17543
  have eq98437 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq97986
       grind)
    | exact superpose eq97986 eq13
    | exact resolve eq13 eq97986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97986
  have eq98586 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq98354
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq98354
    | exact resolve eq98354 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98354
  have eq98606 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq97982 eq98586
    | exact resolve eq98586 eq97982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98586
  have eq100319 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq98606 eq6632
    | exact resolve eq6632 eq98606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6632
  have eq100418 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq98606 eq1828
    | exact resolve eq1828 eq98606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828 eq98606
  have eq100568 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq98006 eq100418
    | exact resolve eq100418 eq98006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100418
  have eq100599 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq30 eq100319
    | exact resolve eq100319 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq100319
  have eq100610 : x = y := by
    first
    | (have r₁ := eq100568
       have r₂ := eq27
       grind)
    | exact resolve eq100568 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100568
  have eq100628 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq97730 eq100599
    | exact resolve eq100599 eq97730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97730 eq100599
  have eq100645 : x = (k y y) := by
    first
    | (have r₁ := eq100628
       have r₂ := eq98437
       grind)
    | exact resolve eq100628 eq98437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98437 eq100628
  have eq100657 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq100610
       grind)
    | exact superpose eq100610 eq24
    | exact resolve eq24 eq100610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq101007 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq100657
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq100657
    | exact resolve eq100657 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100657
  have eq101082 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq97982 eq101007
    | exact resolve eq101007 eq97982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101007
  have eq101720 : x = (k x x) := by
    first
    | (have i₁ := eq100645
       have i₂ := eq100610
       grind)
    | exact superpose eq100610 eq100645
    | exact resolve eq100645 eq100610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100610 eq100645
  have eq101742 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq908 x x
       have i₂ := eq101720
       grind)
    | exact superpose eq101720 eq908
    | (have j0 := eq908 x x
       grind)
    | exact resolve eq908 eq101720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908 eq101720
  have eq101745 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq101742
  have eq101746 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq101745
  have eq101755 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq101746
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq101746
    | exact resolve eq101746 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq101746
  have eq101774 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq97982 eq101755
    | exact resolve eq101755 eq97982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97982 eq101755
  have eq102148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq98006 eq11807
    | exact resolve eq11807 eq98006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11807
  have eq102149 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq102148
       have r₂ := eq27
       grind)
    | exact resolve eq102148 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102148
  have eq102150 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) ≠ (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq98006 eq102149
    | exact resolve eq102149 eq98006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98006 eq102149
  have eq102151 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) ≠ (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq101082 eq102150
    | exact resolve eq102150 eq101082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102150
  have eq102152 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) ≠ (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq6746 eq102151
    | exact resolve eq102151 eq6746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102151
  have eq102153 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq101082 eq102152
    | exact resolve eq102152 eq101082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101082 eq102152
  have eq102154 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6746 eq102153
    | exact resolve eq102153 eq6746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6746 eq102153
  have eq102155 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq101774 eq102154
    | (have r₁ := eq102154
       have r₂ := eq101774
       grind)
    | exact resolve eq102154 eq101774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101774 eq102154
  have eq102311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq102155
  have eq102395 : False := by grind
  exact eq102395

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pxx_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq43 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : x ≠ (M.op x y) ∨ (M.op y y) = (k y x) := by
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
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op (M.op (M.op X2 X1) (M.op X0 X0)) (M.op (M.op X2 X1) (M.op X0 X0))) = (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
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
  clear eq24 eq36
  have eq85 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq90 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq85
    | exact resolve eq85 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq91
    | exact resolve eq91 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq93 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq107 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq109 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq109 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq109 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq113 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq43
    | exact resolve eq43 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq114 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq110 y
       grind)
    | exact superpose eq110 eq73
    | exact resolve eq73 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq117 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq110 sF3
       grind)
    | exact superpose eq110 eq114
    | exact resolve eq114 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq118 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq110 sF2
       grind)
    | exact superpose eq110 eq113
    | exact resolve eq113 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq126 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq99
       have i₂ := eq110 sF3
       grind)
    | exact superpose eq110 eq99
    | exact resolve eq99 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq126
       have i₂ := eq110 y
       grind)
    | exact superpose eq110 eq126
    | exact resolve eq126 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq126
  have eq252 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq252 eq50
    | exact resolve eq50 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq622 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X1) X1 X2 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1013 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) = (M.op (M.op X0 X0) (M.op (M.op X2 X1) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1 X2
       have i₂ := eq53 (M.op X2 X1) (M.op X0 X0)
       grind)
    | exact superpose eq53 eq65
    | (have j0 := eq65 X0 X1 X2
       grind)
    | (have r₁ := eq65 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X1 (M.op X0 X1)) X2
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq65 (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1)) X2
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq65 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1033 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) = (M.op (M.op X1 X1) (M.op (M.op X0 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1013 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1437 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq255 eq50
    | exact resolve eq50 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq1458 : (M.op (M.op x y) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) := by
    first
    | exact superpose eq252 eq1437
    | exact resolve eq1437 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437
  have eq1650 : (M.op x y) = (M.op y (M.op y (M.op y (M.op x y)))) := by
    first
    | exact superpose eq1458 eq260
    | exact resolve eq260 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq1458
  have eq1968 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq622 X0 X0 X0
       grind)
    | exact superpose eq622 eq50
    | exact resolve eq50 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1969 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq622 X0 X0 X0
       grind)
    | exact superpose eq622 eq51
    | exact resolve eq51 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2151 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq584 X0
       have i₂ := eq1968 X0
       grind)
    | exact superpose eq1968 eq584
    | exact resolve eq584 eq1968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2177 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq51 sF4
       have i₂ := eq1968 sF4
       grind)
    | exact superpose eq1968 eq51
    | exact resolve eq51 eq1968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2179 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1968 eq588
    | exact resolve eq588 eq1968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968
  have eq2191 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq588 eq2179
    | exact resolve eq2179 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2179
  have eq2225 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq50 eq2151
    | exact resolve eq2151 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151
  have eq2279 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq2225 X0
       grind)
    | exact superpose eq2225 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq2225 X0
       grind)
    | exact resolve eq13 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225
  have eq2299 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2279 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2279
  have eq2348 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2299 (M.op x (M.op x x))
       have i₂ := eq622 x x x
       grind)
    | exact superpose eq622 eq2299
    | exact resolve eq2299 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq2553 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1969 eq588
    | exact resolve eq588 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969
  have eq2565 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq588 eq2553
    | exact resolve eq2553 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq2553
  have eq6911 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq653 (M.op X0 X0) X1 X2
       have i₂ := eq1033 X0 X0
       grind)
    | exact superpose eq1033 eq653
    | exact resolve eq653 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq1033
  have eq6973 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (k (M.op X0 (M.op X0 X0)) X0)) (k (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6911 X1 X1 X2
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq6911
    | exact resolve eq6911 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq6911
  have eq7062 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6973 X0 X1 X2
       have i₂ := eq2348 X0
       grind)
    | exact superpose eq2348 eq6973
    | exact resolve eq6973 eq2348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2348 eq6973
  have eq7212 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7062 X1 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq584 X0
       grind)
    | exact superpose eq584 eq7062
    | exact resolve eq7062 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq7062
  have eq18999 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq94 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19000 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18999
    | exact resolve eq18999 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18999
  have eq19006 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19000
       have r₂ := eq27
       grind)
    | exact resolve eq19000 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19000
  have eq19008 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19006
    | exact resolve eq19006 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19006
  have eq19010 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19008
    | exact resolve eq19008 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19008
  have eq19012 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19010 eq107
    | (have r₁ := eq107
       have r₂ := eq19010
       grind)
    | exact resolve eq107 eq19010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq19016 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19010 eq50
    | exact resolve eq50 eq19010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19010
  have eq19092 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq19012
  have eq19093 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq19092
  have eq19317 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19016 eq2177
    | exact resolve eq2177 eq19016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177 eq19016
  have eq19854 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19093 eq94
    | exact resolve eq94 eq19093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq19093
  have eq19865 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19854
  have eq19871 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19865 eq19317
    | exact resolve eq19317 eq19865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19317 eq19865
  have eq19907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq19871
  have eq19915 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19907
       have r₂ := eq27
       grind)
    | exact resolve eq19907 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19907
  have eq20052 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k y x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq19915
       grind)
    | exact superpose eq19915 eq106
    | (have r₁ := eq106
       have r₂ := eq19915
       grind)
    | exact resolve eq106 eq19915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq20053 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq118
       have i₂ := eq19915
       grind)
    | exact superpose eq19915 eq118
    | exact resolve eq118 eq19915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq20061 : x = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq19915
       grind)
    | exact superpose eq19915 eq50
    | exact resolve eq50 eq19915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq19915
  have eq20136 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k y x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20052
  have eq20137 : (k y x) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20136
  have eq20167 : x = (M.op y (M.op y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq252 eq20061
    | exact resolve eq20061 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq20061
  have eq20173 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq20053
    | exact resolve eq20053 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20053
  have eq21120 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq20137
       grind)
    | exact superpose eq20137 eq72
    | exact resolve eq72 eq20137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq20137
  have eq21325 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20167 eq1650
    | exact resolve eq1650 eq20167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650 eq20167
  have eq22501 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21120
       have i₂ := eq21325
       grind)
    | exact superpose eq21325 eq21120
    | exact resolve eq21120 eq21325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21120 eq21325
  have eq22552 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22501
  have eq22567 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq22552
    | exact resolve eq22552 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22552
  have eq22919 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22567 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq22567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22567
  have eq22922 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq22919
    | exact resolve eq22919 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22919
  have eq22928 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22922
       have r₂ := eq27
       grind)
    | exact resolve eq22922 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22922
  have eq22930 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq22928
    | exact resolve eq22928 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22928
  have eq22932 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq22930
    | exact resolve eq22930 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22930
  have eq22933 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22932
  have eq23016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22933 eq20173
    | exact resolve eq20173 eq22933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20173 eq22933
  have eq23103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq23016
  have eq23127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23103
       have r₂ := eq27
       grind)
    | exact resolve eq23103 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23103
  have eq23363 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23127 eq64
    | (have r₁ := eq64
       have r₂ := eq23127
       grind)
    | exact resolve eq64 eq23127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq23397 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23127 eq2565
    | exact resolve eq2565 eq23127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2565
  have eq23401 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq23363
  have eq23403 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq23397
    | exact resolve eq23397 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23397
  have eq23450 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23403 eq2299
    | exact resolve eq2299 eq23403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2299 eq23403
  have eq23522 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23127 eq23450
    | exact resolve eq23450 eq23127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23127 eq23450
  have eq23534 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq23522
  have eq23550 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23534 eq90
    | exact resolve eq90 eq23534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23534
  have eq23574 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq23550
    | exact resolve eq23550 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq23550
  have eq24704 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23401 eq90
    | exact resolve eq90 eq23401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq23401
  have eq24726 : (M.op y y) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq24704
    | exact resolve eq24704 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq24704
  have eq24729 : (M.op y y) = (k y x) := by
    first
    | (have r₁ := eq24726
       have r₂ := eq63
       grind)
    | exact resolve eq24726 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq24726
  have eq24730 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24729
       have i₂ := eq23574
       grind)
    | exact superpose eq23574 eq24729
    | exact resolve eq24729 eq23574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23574 eq24729
  have eq25214 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7212 y y
       have i₂ := eq24730
       grind)
    | exact superpose eq24730 eq7212
    | exact resolve eq7212 eq24730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24730
  have eq25228 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25214
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25214
    | exact resolve eq25214 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25214
  have eq25229 : x = (M.op x y) := by grind
  clear eq25228
  have eq25393 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq25229 eq20
    | exact resolve eq20 eq25229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq25475 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq25229 eq2191
    | exact resolve eq2191 eq25229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2191
  have eq25498 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq25475
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25475
    | exact resolve eq25475 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq25475
  have eq25550 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq25393
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25393
    | exact resolve eq25393 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25393
  have eq25551 : x = (M.op y y) := by
    first
    | exact superpose eq25229 eq25498
    | exact resolve eq25498 eq25229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25229 eq25498
  have eq25586 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq25550 eq26
    | exact resolve eq26 eq25550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq25842 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq25551
       grind)
    | exact superpose eq25551 eq117
    | exact resolve eq117 eq25551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq25551
  have eq25978 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq25842
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25842
    | exact resolve eq25842 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq25842
  have eq26000 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq25550 eq25978
    | exact resolve eq25978 eq25550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25550 eq25978
  have eq26152 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26000 eq7212
    | exact resolve eq7212 eq26000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7212 eq26000
  have eq26166 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25586 eq26152
    | exact resolve eq26152 eq25586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25586 eq26152
  have eq26201 : False := by grind
  exact eq26201

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq52 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq52
    | exact resolve eq52 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq83 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq83 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq83 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq83 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq90 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq85 (σ X0)
       grind)
    | exact superpose eq85 eq15
    | exact resolve eq15 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq90
    | exact resolve eq90 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq90
  have eq116 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq9
    | exact resolve eq9 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq134 (σ X1) (σ X0)
       grind)
    | exact superpose eq134 eq15
    | (have j1 := eq134 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq169 X0 X1
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq169
    | (have j0 := eq169 X0 X1
       grind)
    | exact resolve eq169 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq189 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq255 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq73 X1 X1
       grind)
    | exact superpose eq73 eq189
    | exact resolve eq189 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq413 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op (M.op X2 X1) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq116 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq73 X0 X0
       grind)
    | exact superpose eq73 eq116
    | exact resolve eq116 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq446 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq51 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq51 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq51 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq51 eq9
    | exact resolve eq9 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq496 X0 X1 X2 X3
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq496
    | exact resolve eq496 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq533 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq472 X0 X1 X2 X3 X4
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq472
    | exact resolve eq472 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq600 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq446 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq446 X0 X0 X0
       grind)
    | exact superpose eq446 eq446
    | exact resolve eq446 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq446 X0 X0 X0
       grind)
    | exact superpose eq446 eq9
    | exact resolve eq9 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq255 X2 X3
       have i₂ := eq629 X2 X0 X1
       grind)
    | exact superpose eq629 eq255
    | exact resolve eq255 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq174 x y
       grind)
    | exact superpose eq174 eq16
    | (have j1 := eq174 x y
       grind)
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq5299 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X3 X2 X3 X2
       have i₂ := eq523 X2 X3 X0 X1
       grind)
    | exact superpose eq523 eq69
    | exact resolve eq69 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq5581 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq777
       have i₂ := eq134 y x
       grind)
    | exact superpose eq134 eq777
    | (have j1 := eq134 y x
       grind)
    | exact resolve eq777 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq777
  have eq5582 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq5581
  have eq11345 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq600 (M.op X0 (M.op X0 X0)) X1 (M.op X2 X0)
       have i₂ := eq255 X0 X2
       grind)
    | exact superpose eq255 eq600
    | exact resolve eq600 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11423 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X2 X2))) = (M.op (M.op X2 X2) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq533 X2 X2 X3 X4 X5
       have i₂ := eq600 X2 X0 X1
       grind)
    | exact superpose eq600 eq533
    | exact resolve eq533 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq11814 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11423 X0 X1 X2 x x x
       have i₂ := eq446 (M.op x x) x X2
       grind)
    | (have i₁ := eq11423 X0 X1 X2 x x x
       have i₂ := eq446 X0 x (M.op (M.op (M.op x x) (M.op x x)) (M.op x (M.op X2 X2)))
       grind)
    | exact superpose eq446 eq11423
    | exact resolve eq11423 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq11423
  have eq11864 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11345 X0 X1 X2
       have i₂ := eq52 X2 X0
       grind)
    | exact superpose eq52 eq11345
    | exact resolve eq11345 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11345
  have eq12021 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11864 X0 X1 X2
       have i₂ := eq52 X0 (M.op X0 X0)
       grind)
    | exact superpose eq52 eq11864
    | exact resolve eq11864 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11864
  have eq12087 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12021 X0 X1 X2
       have i₂ := eq255 X0 X0
       grind)
    | exact superpose eq255 eq12021
    | exact resolve eq12021 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12021
  have eq12123 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12087 X0 X1 X2
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq12087
    | exact resolve eq12087 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq12087
  have eq12192 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12123 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq600 X0 x X1
       grind)
    | exact superpose eq600 eq12123
    | exact resolve eq12123 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12123
  have eq12434 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12192 X0 X1 X2
       have i₂ := eq255 X0 X1
       grind)
    | exact superpose eq255 eq12192
    | exact resolve eq12192 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12192
  have eq12498 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12434 X0 X1 X2
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq12434
    | exact resolve eq12434 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12434
  have eq16669 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5299 (M.op X1 X1) (M.op x x) X1 (M.op X0 X0)
       have i₂ := eq51 X1 x x X0
       grind)
    | exact superpose eq51 eq5299
    | exact resolve eq5299 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq16682 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5299 X3 X2 (M.op X1 (M.op X2 X3)) (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq9 eq5299
    | exact resolve eq5299 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16855 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op X0 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16682 X0 X1 X2 X3
       have i₂ := eq12498 X0 X3 X0
       grind)
    | exact superpose eq12498 eq16682
    | exact resolve eq16682 eq12498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16682
  have eq16865 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16669 X0 X1
       have i₂ := eq12498 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq12498 eq16669
    | exact resolve eq16669 eq12498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12498 eq16669
  have eq17329 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16865 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq600 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq600 eq16865
    | exact resolve eq16865 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq17349 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X2 (M.op X1 X1)) X0) (M.op (M.op X2 (M.op X1 X1)) X0))) = (M.op (M.op (M.op X2 (M.op X1 X1)) X0) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16865 (M.op (M.op X2 (M.op X1 X1)) X0) X1
       have i₂ := eq629 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq629 eq16865
    | exact resolve eq16865 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq17681 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X2 (M.op X1 X1)) X0) (M.op (M.op X2 (M.op X1 X1)) X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17349 X0 X1 X2
       have i₂ := eq255 X0 (M.op X2 (M.op X1 X1))
       grind)
    | exact superpose eq255 eq17349
    | exact resolve eq17349 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17349
  have eq17700 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17329 X0 X1
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq17329
    | exact resolve eq17329 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17329
  have eq17776 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X1 X1)) X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17681 X0 X1 X2
       have i₂ := eq52 (M.op X2 (M.op X1 X1)) X0
       grind)
    | exact superpose eq52 eq17681
    | exact resolve eq17681 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq17681
  have eq17794 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17700 X0 X1
       have i₂ := eq255 X0 X1
       grind)
    | exact superpose eq255 eq17700
    | exact resolve eq17700 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq17700
  have eq17985 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17794 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq715 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq715 eq17794
    | exact resolve eq17794 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715 eq17794
  have eq40333 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X2)) = (τ (M.op X0 (M.op (M.op X1 X0) (σ X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X2 (M.op X2 X2))
       have i₂ := eq413 X2 X0 X1
       grind)
    | exact superpose eq413 eq10
    | exact resolve eq10 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq51949 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17776 (M.op X0 X0) X1 x
       have i₂ := eq16855 X0 x X1 X1
       grind)
    | exact superpose eq16855 eq17776
    | exact resolve eq17776 eq16855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16855 eq17776
  have eq107338 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51949 X1 X2
       have i₂ := eq17985 (M.op X1 (M.op X2 X1)) X1 X0
       grind)
    | (have i₁ := eq51949 X1 X1
       have i₂ := eq17985 (M.op X1 (M.op X1 X1)) X1 X1
       grind)
    | exact superpose eq17985 eq51949
    | exact resolve eq51949 eq17985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17985 eq51949
  have eq175524 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq107338 X2 X3 X2
       have i₂ := eq523 X2 X3 X0 X1
       grind)
    | exact superpose eq523 eq107338
    | exact resolve eq107338 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523 eq107338
  have eq238513 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op (M.op X1 X0) (σ (M.op x x))))) ∨ (M.op x y) = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq175524 X0 X1 (σ x) (σ y)
       have i₂ := eq5582
       grind)
    | exact superpose eq5582 eq175524
    | exact resolve eq175524 eq5582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5582
  have eq241008 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq238513 x x
       have i₂ := eq116 x x x
       grind)
    | exact superpose eq116 eq238513
    | exact resolve eq238513 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq238513
  have eq241557 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq241008
       have i₂ := eq97 y
       grind)
    | exact superpose eq97 eq241008
    | exact resolve eq241008 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241008
  have eq241827 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq241557
       have i₂ := eq97 x
       grind)
    | exact superpose eq97 eq241557
    | exact resolve eq241557 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241557
  have eq463514 : ∀ X0 X1 : G, (M.op (M.op y y) (M.op (M.op y y) (M.op y y))) = (τ (M.op X0 (M.op (M.op X1 X0) (σ (M.op x x))))) ∨ (M.op x y) = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq40333 X0 X1 (M.op y y)
       have i₂ := eq241827
       grind)
    | exact superpose eq241827 eq40333
    | exact resolve eq40333 eq241827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241827
  have eq463562 : (M.op (M.op y y) (M.op (M.op y y) (M.op y y))) = (M.op (M.op x x) (M.op (M.op x x) (M.op x x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq463514 x x
       have i₂ := eq40333 x x (M.op x x)
       grind)
    | exact superpose eq40333 eq463514
    | exact resolve eq463514 eq40333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40333 eq463514
  have eq463721 : (M.op (M.op y y) (M.op (M.op y y) (M.op y y))) = (M.op x (M.op (M.op x x) (M.op x x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq463562
       have i₂ := eq16865 (M.op x x) x
       grind)
    | exact superpose eq16865 eq463562
    | exact resolve eq463562 eq16865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463562
  have eq463770 : x = (M.op (M.op y y) (M.op (M.op y y) (M.op y y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq463721
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq463721
    | exact resolve eq463721 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463721
  have eq463782 : x = (M.op y (M.op (M.op y y) (M.op y y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq463770
       have i₂ := eq16865 (M.op y y) y
       grind)
    | exact superpose eq16865 eq463770
    | exact resolve eq463770 eq16865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16865 eq463770
  have eq463783 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq463782
       have i₂ := eq9 y y y
       grind)
    | exact superpose eq9 eq463782
    | exact resolve eq463782 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463782
  have eq464021 : ∀ X0 X1 : G, (M.op y y) = (M.op x (M.op X0 (M.op (M.op X1 X0) (M.op x x)))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq175524 X0 X1 x y
       have i₂ := eq463783
       grind)
    | exact superpose eq463783 eq175524
    | exact resolve eq175524 eq463783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175524 eq463783
  have eq464069 : (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq464021 x x
       have i₂ := eq5299 x x x x
       grind)
    | exact superpose eq5299 eq464021
    | exact resolve eq464021 eq5299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5299 eq464021
  have eq464574 : ∀ X0 : G, y = (M.op (M.op x x) (M.op (M.op X0 (M.op x x)) (M.op x x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11814 X0 y y
       have i₂ := eq464069
       grind)
    | exact superpose eq464069 eq11814
    | exact resolve eq11814 eq464069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11814 eq464069
  have eq464780 : x = y ∨ x = y := by
    first
    | (have i₁ := eq464574 x
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq464574
    | exact resolve eq464574 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464574
  have eq464781 : x = y := by grind
  clear eq464780
  have eq464943 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq464781
       grind)
    | exact superpose eq464781 eq16
    | exact resolve eq16 eq464781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464781
  have eq464945 : False := by grind
  exact eq464945
