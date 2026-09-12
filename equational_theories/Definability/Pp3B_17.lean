import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pyx_pxx_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq9 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ X0) (σ X1)
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq46 (τ X0)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq86 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq86
    | exact resolve eq86 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq86
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq106 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq201 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq98 X1
       grind)
    | exact superpose eq98 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq202 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq201 X0 X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq201
    | (have j0 := eq201 X0 X1
       grind)
    | exact resolve eq201 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq232 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq202 y x
       grind)
    | exact superpose eq202 eq16
    | (have j1 := eq202 y x
       grind)
    | exact resolve eq16 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq663 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq232
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq232
    | (have j1 := eq59 y x
       grind)
    | exact resolve eq232 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq232
  have eq664 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq663
  have eq9879 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq664
       grind)
    | exact superpose eq664 eq10
    | exact resolve eq10 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq9919 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq9879
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq9879
    | exact resolve eq9879 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9879
  have eq9920 : (M.op y y) = (M.op x x) := by grind
  clear eq9919
  have eq10000 : ∀ X0 : G, y = (M.op (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) X0)) := by
    intro X0
    first
    | (have i₁ := eq106 y y x
       have i₂ := eq9920
       grind)
    | exact superpose eq9920 eq106
    | exact resolve eq106 eq9920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq9920
  have eq10046 : x = y := by
    first
    | (have i₁ := eq10000 x
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq10000
    | exact resolve eq10000 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10000
  have eq10070 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10046
       grind)
    | exact superpose eq10046 eq16
    | exact resolve eq16 eq10046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10046
  have eq10071 : False := by grind
  exact eq10071

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq38 X0 X1 X2 X3
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X0 X1 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq132 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq58
    | exact resolve eq58 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq215 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X3 (M.op X0 X0)
       have i₂ := eq19 X0 X1 X2
       grind)
    | (have i₁ := eq21 X1 X1 (M.op X1 X2)
       have i₂ := eq19 X1 X1 X2
       grind)
    | exact superpose eq19 eq21
    | exact resolve eq21 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq21
  have eq351 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op (M.op (M.op (σ X0) (σ X1)) X2) (M.op X2 X3)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq52 (σ X0) (σ X1) X2 X3
       grind)
    | exact superpose eq52 eq15
    | (have j1 := eq52 (σ X0) (σ X1) X2 X3
       grind)
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2396 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq215 X1 X0 x (M.op X1 X0)
       have i₂ := eq52 X1 X0 (M.op X1 X0) (M.op X0 x)
       grind)
    | exact superpose eq52 eq215
    | (have j1 := eq52 X1 X0 x x
       grind)
    | exact resolve eq215 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq2446 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2396 X0 X1
       have j1 := eq140 X1 X0
       grind)
    | (have r₁ := eq2396 X0 X1
       have r₂ := eq140 X0 X1
       grind)
    | (have r₁ := eq2396 X1 X0
       have r₂ := eq140 X0 X1
       grind)
    | exact resolve eq2396 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq2396
  have eq3427 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq3428 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3427 X0 X1
       have i₂ := eq2446 X1 X0
       grind)
    | exact superpose eq2446 eq3427
    | (have j0 := eq3427 X0 X1
       grind)
    | exact resolve eq3427 eq2446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3427
  have eq7115 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq215 (σ X1) (σ X0) x (M.op (σ X1) (σ X0))
       have i₂ := eq351 X1 X0 (M.op (σ X1) (σ X0)) (M.op (σ X0) x)
       grind)
    | exact superpose eq351 eq215
    | (have j1 := eq351 X1 X0 x x
       grind)
    | exact resolve eq215 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq351
  have eq7251 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7115 X0 X1
       have i₂ := eq2446 X0 X1
       grind)
    | exact superpose eq2446 eq7115
    | (have j0 := eq7115 X0 X1
       grind)
    | exact resolve eq7115 eq2446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2446 eq7115
  have eq7381 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7251 X0 X1
       have j1 := eq3428 X1 X0
       grind)
    | (have r₁ := eq7251 X0 X1
       have r₂ := eq3428 X0 X1
       grind)
    | (have r₁ := eq7251 X1 X0
       have r₂ := eq3428 X0 X1
       grind)
    | exact resolve eq7251 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3428 eq7251
  have eq7451 : False := by grind
  exact eq7451

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq250 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq250 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq250
    | (have j0 := eq250 (σ X0) (σ X1)
       grind)
    | exact resolve eq250 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4602 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq251 X0 X1
       have i₂ := eq250 X0 X1
       grind)
    | exact superpose eq250 eq251
    | (have j0 := eq251 X0 X1
       have j1 := eq250 (σ X0) (σ X1)
       grind)
    | exact resolve eq251 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15949 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4602 x y
       grind)
    | exact superpose eq4602 eq16
    | (have j1 := eq4602 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq4602 x y
       grind)
    | exact resolve eq16 eq4602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4602
  have eq16027 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15949
  have eq16039 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16027
       grind)
    | exact superpose eq16027 eq16
    | exact resolve eq16 eq16027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16042 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq16027
       grind)
    | exact superpose eq16027 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq16027
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq16027
       grind)
    | exact resolve eq13 eq16027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16095 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16042
  have eq16098 : (σ x) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16095
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq16095
    | exact resolve eq16095 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16095
  have eq16100 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq250 eq16098
    | (have j1 := eq250 (σ y) (σ x)
       grind)
    | exact resolve eq16098 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16098
  have eq16101 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16100
       have r₂ := eq16039
       grind)
    | exact resolve eq16100 eq16039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16100
  have eq16104 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq16101
       grind)
    | exact superpose eq16101 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq16101
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq16101
       grind)
    | exact resolve eq12 eq16101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16101
  have eq16158 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16104
  have eq16159 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16158
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq16158
    | exact resolve eq16158 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16158
  have eq16160 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16027 eq16159
    | exact resolve eq16159 eq16027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16027 eq16159
  have eq16161 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq250 eq16160
    | (have j1 := eq250 x y
       grind)
    | exact resolve eq16160 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq16160
  have eq16162 : x = (M.op x y) := by
    first
    | (have r₁ := eq16161
       have r₂ := eq16039
       grind)
    | exact resolve eq16161 eq16039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16039 eq16161
  have eq16163 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16162
       grind)
    | exact superpose eq16162 eq16
    | exact resolve eq16 eq16162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16166 : x ≠ x ∨ y = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq16162
       grind)
    | exact superpose eq16162 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq16162
       grind)
    | exact resolve eq13 eq16162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16218 : y = (M.op y x) ∨ x = (k x y) := by grind
  clear eq16166
  have eq16623 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq16218
       grind)
    | exact superpose eq16218 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq16218
       grind)
    | exact resolve eq12 eq16218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16218
  have eq16677 : (M.op x y) = (k x y) ∨ x = (k x y) := by grind
  clear eq16623
  have eq16687 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16677
       have i₂ := eq16162
       grind)
    | exact superpose eq16162 eq16677
    | exact resolve eq16677 eq16162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16162 eq16677
  have eq16688 : x = (k x y) := by grind
  clear eq16687
  have eq16706 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq251 x y
       have i₂ := eq16688
       grind)
    | exact superpose eq16688 eq251
    | (have j0 := eq251 x y
       grind)
    | exact resolve eq251 eq16688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq16688
  have eq16709 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16706
  have eq16711 : False := by grind
  exact eq16711

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pxy_pyx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  clear eq36
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op y y) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81
    | exact resolve eq81 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq87 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq86
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq328 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq107 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq107
    | (have j0 := eq107 (σ X0)
       grind)
    | exact resolve eq107 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq107 x
       grind)
    | exact superpose eq107 eq44
    | (have j1 := eq107 x
       grind)
    | exact resolve eq44 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq397 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq602 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) X3) (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X0 X0) X1 X2
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq51 (M.op X2 X2) X1 X2
       have i₂ := eq51 X2 X2 X2
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)))) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) X1 X3
       have i₂ := eq55 X1 X0 X2
       grind)
    | exact superpose eq55 eq51
    | exact resolve eq51 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq647 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq602 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq602
    | exact resolve eq602 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq1025 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq195 X0
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq195 X2
       have i₂ := eq51 X2 X2 X2
       grind)
    | exact superpose eq51 eq195
    | exact resolve eq195 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq3334 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq397 X0 X1 X2
       have i₂ := eq195 X0
       grind)
    | exact superpose eq195 eq397
    | exact resolve eq397 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq397
  have eq7016 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq328 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq30139 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) x) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq606 X0 X1 X2 X3
       have i₂ := eq1025 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))
       grind)
    | exact superpose eq1025 eq606
    | exact resolve eq606 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq1025
  have eq30518 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2)) x) (M.op x y)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2)) x) (M.op x y))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq647 X0 X1 x
       have i₂ := eq30139 (M.op X0 X1) X1 X2 x
       grind)
    | exact superpose eq30139 eq647
    | exact resolve eq647 eq30139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647 eq30139
  have eq30770 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq3334 eq30518
    | exact resolve eq30518 eq3334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334 eq30518
  have eq71203 : ∀ X0 : G, y = (M.op (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) X0)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq30770 y y x
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq30770
    | exact resolve eq30770 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq71226 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq71203 x
       have i₂ := eq14 x (M.op x x) x
       grind)
    | exact superpose eq14 eq71203
    | exact resolve eq71203 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71203
  have eq71360 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq71226 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq71226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq71360
    | exact resolve eq71360 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71360
  have eq71372 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq71361
       have r₂ := eq28
       grind)
    | exact resolve eq71361 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71361
  have eq71492 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ x)) X0)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq71372 eq30770
    | exact resolve eq30770 eq71372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71372
  have eq71515 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq71492 x
       have i₂ := eq14 sF2 (M.op sF2 sF2) x
       grind)
    | exact superpose eq14 eq71492
    | exact resolve eq71492 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71492
  have eq71657 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq71515
  have eq71833 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq71657
    | exact resolve eq71657 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71657
  have eq72213 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq71833 eq71226
    | exact resolve eq71226 eq71833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71226 eq71833
  have eq72215 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq72213
  have eq72217 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq72215
       have r₂ := eq28
       grind)
    | exact resolve eq72215 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72215
  have eq72237 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq72217
  have eq72410 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq72237
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72237
    | exact resolve eq72237 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72237
  have eq72423 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq72410
       grind)
    | exact superpose eq72410 eq45
    | exact resolve eq45 eq72410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq72410
  have eq72441 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq72423
    | exact resolve eq72423 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72423
  have eq72479 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq72441 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq72441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72482 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq72479
    | exact resolve eq72479 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72479
  have eq72493 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq72482
       have r₂ := eq28
       grind)
    | exact resolve eq72482 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72482
  have eq241344 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ x)) X0)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq72493 eq30770
    | exact resolve eq30770 eq72493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30770 eq72493
  have eq241387 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq241344 x
       have i₂ := eq14 sF2 (M.op sF2 sF2) x
       grind)
    | exact superpose eq14 eq241344
    | exact resolve eq241344 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241344
  have eq241388 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq241387
  have eq241581 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq241388
  have eq241803 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq241581
    | exact resolve eq241581 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241581
  have eq241848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq241803 eq72441
    | exact resolve eq72441 eq241803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72441 eq241803
  have eq241882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq241848
  have eq241894 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq241882
       have r₂ := eq28
       grind)
    | exact resolve eq241882 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241882
  have eq241897 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq241894 eq30
    | exact resolve eq30 eq241894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq241894
  have eq242065 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq241897
    | exact resolve eq241897 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq241897
  have eq242066 : x = y := by grind
  clear eq242065
  have eq242069 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq242066
       grind)
    | exact superpose eq242066 eq19
    | exact resolve eq19 eq242066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq242070 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq242066
       grind)
    | exact superpose eq242066 eq25
    | exact resolve eq25 eq242066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq242066
  have eq242354 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq242070
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq242070
    | exact resolve eq242070 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242070
  have eq242357 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq242354 eq27
    | exact resolve eq27 eq242354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq242354
  have eq242532 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq332
       have i₂ := eq242069
       grind)
    | exact superpose eq242069 eq332
    | exact resolve eq332 eq242069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq242599 : (k (M.op x y) x) = (M.op (M.op x y) x) := by grind
  have eq242801 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq242532
    | exact resolve eq242532 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242532
  have eq242841 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq247330 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq242801 eq107
    | (have j0 := eq107 (σ x)
       grind)
    | exact resolve eq107 eq242801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq247331 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq242357 eq247330
    | exact resolve eq247330 eq242357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247330
  have eq247345 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq247331
       have r₂ := eq28
       grind)
    | exact resolve eq247331 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247331
  have eq247351 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq242357 eq247345
    | exact resolve eq247345 eq242357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247345
  have eq247444 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq247351 eq242841
    | exact resolve eq242841 eq247351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242841 eq247351
  have eq247448 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq242357 eq247444
    | exact resolve eq247444 eq242357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247444
  have eq247825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq247448 eq242801
    | exact resolve eq242801 eq247448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242801 eq247448
  have eq247831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq247825
  have eq247834 : x = (M.op x y) := by
    first
    | (have r₁ := eq247831
       have r₂ := eq28
       grind)
    | exact resolve eq247831 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247831
  have eq247845 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq247834 eq21
    | exact resolve eq21 eq247834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq248258 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq247834 eq242599
    | exact resolve eq242599 eq247834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242599
  have eq248263 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq248258
       have i₂ := eq242069
       grind)
    | exact superpose eq242069 eq248258
    | exact resolve eq248258 eq242069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242069 eq248258
  have eq248444 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq247845
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq247845
    | exact resolve eq247845 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247845
  have eq248447 : x = (k x x) := by
    first
    | exact superpose eq247834 eq248263
    | exact resolve eq248263 eq247834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247834 eq248263
  have eq249077 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7016 x
       have i₂ := eq248447
       grind)
    | exact superpose eq248447 eq7016
    | (have j0 := eq7016 x
       grind)
    | exact resolve eq7016 eq248447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7016 eq248447
  have eq249081 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq249077
  have eq249088 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq249081
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq249081
    | exact resolve eq249081 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq249081
  have eq249106 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq242357 eq249088
    | exact resolve eq249088 eq242357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242357 eq249088
  have eq249122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq248444 eq249106
    | exact resolve eq249106 eq248444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248444 eq249106
  have eq249136 : False := by grind
  exact eq249136

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pxx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  clear eq36
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81
    | exact resolve eq81 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq86
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq336 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq110 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq110
    | (have j0 := eq110 (σ X0)
       grind)
    | exact resolve eq110 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq44
    | (have j1 := eq110 x
       grind)
    | exact resolve eq44 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq405 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq612 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) X3) (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X0 X0) X1 X2
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq51 (M.op X2 X2) X1 X2
       have i₂ := eq51 X2 X2 X2
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq622 : ∀ X0 : G, (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq51 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x y X0
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y) X0
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X0)
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq53 (M.op X2 X2)
       have i₂ := eq51 X2 X2 X2
       grind)
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq661 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq612 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq612
    | exact resolve eq612 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq1070 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq199 X0
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq199 X2
       have i₂ := eq51 X2 X2 X2
       grind)
    | exact superpose eq51 eq199
    | exact resolve eq199 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1207 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq203 X0
       have i₂ := eq199 X0
       grind)
    | exact superpose eq199 eq203
    | exact resolve eq203 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq1215 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) x) (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq1207 eq14
    | exact resolve eq14 eq1207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1392 : ∀ X0 : G, (M.op (M.op x x) (M.op x y)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq622 X0
       have i₂ := eq199 x
       grind)
    | exact superpose eq199 eq622
    | exact resolve eq622 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq1397 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op x y) (M.op y X0))) x) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1392 eq55
    | exact resolve eq55 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1399 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1392 eq14
    | exact resolve eq14 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq1472 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq623 X0
       have i₂ := eq199 sF2
       grind)
    | exact superpose eq199 eq623
    | exact resolve eq623 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq1481 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1472 eq1215
    | exact resolve eq1215 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215 eq1472
  have eq3436 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq405 X0 X1 X2
       have i₂ := eq199 X0
       grind)
    | exact superpose eq199 eq405
    | exact resolve eq405 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq405
  have eq3560 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) x) := by
    first
    | exact superpose eq1399 eq3436
    | exact resolve eq3436 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3562 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1481 eq3436
    | exact resolve eq3436 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4850 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq3562 eq643
    | exact resolve eq643 eq3562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3562
  have eq5027 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq3436 eq4850
    | exact resolve eq4850 eq3436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3436 eq4850
  have eq7293 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq336 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq14792 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op x y) (M.op y X1))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq1397 X1 (M.op X0 X0)
       have i₂ := eq1070 X0 X0 X0
       grind)
    | exact superpose eq1070 eq1397
    | exact resolve eq1397 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq14915 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 x) x) (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq14792 X0 x
       have i₂ := eq1070 (M.op X0 x) sF0 (M.op y x)
       grind)
    | exact superpose eq1070 eq14792
    | exact resolve eq14792 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070 eq14792
  have eq53707 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq53707
    | exact resolve eq53707 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53707
  have eq53719 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq53708
       have r₂ := eq28
       grind)
    | exact resolve eq53708 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53708
  have eq53721 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq53719
    | exact resolve eq53719 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53719
  have eq53754 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) x) (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq53721 eq643
    | exact resolve eq643 eq53721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53721
  have eq53804 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq5027 eq53754
    | exact resolve eq53754 eq5027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53754
  have eq53923 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq53804 eq661
    | exact resolve eq661 eq53804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53804
  have eq53964 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1481 eq53923
    | exact resolve eq53923 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53923
  have eq54246 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq53964
  have eq54424 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq54246
    | exact resolve eq54246 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54246
  have eq54718 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq54424 eq89
    | exact resolve eq89 eq54424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq54424
  have eq54726 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq54718
  have eq54728 : (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq54726
       have r₂ := eq28
       grind)
    | exact resolve eq54726 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54726
  have eq54744 : (M.op y y) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14915 y
       have i₂ := eq54728
       grind)
    | exact superpose eq54728 eq14915
    | exact resolve eq14915 eq54728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14915 eq54728
  have eq54852 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3560 eq54744
    | exact resolve eq54744 eq3560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3560 eq54744
  have eq54962 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) (M.op y X0))) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq661 y y x
       have i₂ := eq54852
       grind)
    | exact superpose eq54852 eq661
    | exact resolve eq661 eq54852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54852
  have eq55005 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1399 eq54962
    | exact resolve eq54962 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399 eq54962
  have eq55061 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq55005
  have eq55239 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55061
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55061
    | exact resolve eq55061 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55061
  have eq55522 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq55239
       grind)
    | exact superpose eq55239 eq45
    | exact resolve eq45 eq55239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq55239
  have eq55540 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq55522
    | exact resolve eq55522 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55522
  have eq55823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq55540 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq55540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55826 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq55823
    | exact resolve eq55823 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55823
  have eq55837 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq55826
       have r₂ := eq28
       grind)
    | exact resolve eq55826 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55826
  have eq55839 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq55837
    | exact resolve eq55837 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55837
  have eq70960 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) x) (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq55839 eq643
    | exact resolve eq643 eq55839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq55839
  have eq71013 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5027 eq70960
    | exact resolve eq70960 eq5027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5027 eq70960
  have eq71141 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq71013 eq661
    | exact resolve eq661 eq71013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq71013
  have eq71190 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1481 eq71141
    | exact resolve eq71141 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481 eq71141
  have eq71191 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq71190
  have eq72097 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq71191
  have eq72288 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq72097
    | exact resolve eq72097 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72097
  have eq72331 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq72288 eq55540
    | exact resolve eq55540 eq72288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55540 eq72288
  have eq72337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq72331
  have eq72347 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq72337
       have r₂ := eq28
       grind)
    | exact resolve eq72337 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72337
  have eq74482 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq72347 eq30
    | exact resolve eq30 eq72347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq72347
  have eq74618 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq74482
    | exact resolve eq74482 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq74482
  have eq74619 : x = y := by grind
  clear eq74618
  have eq74621 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq74619
       grind)
    | exact superpose eq74619 eq19
    | exact resolve eq19 eq74619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq74622 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq74619
       grind)
    | exact superpose eq74619 eq25
    | exact resolve eq25 eq74619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq74619
  have eq74768 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq74622
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq74622
    | exact resolve eq74622 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74622
  have eq74771 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq74768 eq27
    | exact resolve eq27 eq74768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq74768
  have eq75576 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq340
       have i₂ := eq74621
       grind)
    | exact superpose eq74621 eq340
    | exact resolve eq340 eq74621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq75619 : (M.op (M.op x y) x) = (k (M.op x y) x) := by grind
  have eq75807 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq75576
    | exact resolve eq75576 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75576
  have eq75833 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq79138 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75807 eq110
    | (have j0 := eq110 (σ x)
       grind)
    | exact resolve eq110 eq75807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq79139 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74771 eq79138
    | exact resolve eq79138 eq74771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79138
  have eq79151 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq79139
       have r₂ := eq28
       grind)
    | exact resolve eq79139 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79139
  have eq79157 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74771 eq79151
    | exact resolve eq79151 eq74771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79151
  have eq79208 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq79157 eq75833
    | exact resolve eq75833 eq79157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75833 eq79157
  have eq79210 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74771 eq79208
    | exact resolve eq79208 eq74771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79208
  have eq80022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq79210 eq75807
    | exact resolve eq75807 eq79210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75807 eq79210
  have eq80026 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq80022
  have eq80028 : x = (M.op x y) := by
    first
    | (have r₁ := eq80026
       have r₂ := eq28
       grind)
    | exact resolve eq80026 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80026
  have eq80041 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq80028 eq21
    | exact resolve eq21 eq80028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq80244 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq80028 eq75619
    | exact resolve eq75619 eq80028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75619
  have eq80250 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq80244
       have i₂ := eq74621
       grind)
    | exact superpose eq74621 eq80244
    | exact resolve eq80244 eq74621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74621 eq80244
  have eq80344 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq80041
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq80041
    | exact resolve eq80041 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80041
  have eq80347 : x = (k x x) := by
    first
    | exact superpose eq80028 eq80250
    | exact resolve eq80250 eq80028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80028 eq80250
  have eq80786 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7293 x
       have i₂ := eq80347
       grind)
    | exact superpose eq80347 eq7293
    | (have j0 := eq7293 x
       grind)
    | exact resolve eq7293 eq80347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7293 eq80347
  have eq80790 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq80786
  have eq80796 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq80790
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq80790
    | exact resolve eq80790 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq80790
  have eq80808 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq74771 eq80796
    | exact resolve eq80796 eq74771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74771 eq80796
  have eq80819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq80344 eq80808
    | exact resolve eq80808 eq80344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80344 eq80808
  have eq80828 : False := by grind
  exact eq80828

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxx_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq9 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq46 (σ X0)
       grind)
    | exact superpose eq46 eq15
    | exact resolve eq15 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq46 (τ X0)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq48
    | exact resolve eq48 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq53
    | exact resolve eq53 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq72 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq83 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq84 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq80 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq80 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq87 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq82 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq82 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq83 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq83 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq83 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq95 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X1
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq65
    | (have j0 := eq65 X0 X1
       grind)
    | exact resolve eq65 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq100 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq90 X0 X1
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq90 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq103 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq106 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 X1
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq100
    | (have j0 := eq100 X0 X1
       grind)
    | exact resolve eq100 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq100
  have eq134 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq168 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq10
    | exact resolve eq10 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq175 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 (M.op (M.op X0 X0) (M.op X0 X0)) X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq87
    | exact resolve eq87 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq87 (τ X0) X1
       grind)
    | exact superpose eq87 eq18
    | (have j1 := eq87 (τ X0) X1
       grind)
    | exact resolve eq18 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq87
  have eq272 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq224 X0 X1
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq224
    | (have j0 := eq224 X0 X1
       grind)
    | exact resolve eq224 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq342 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq106 (σ X0) (σ X1)
       grind)
    | exact superpose eq106 eq15
    | (have j1 := eq106 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X0 X1
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq342
    | (have j0 := eq342 X0 X1
       grind)
    | exact resolve eq342 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq385 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op (σ (M.op X1 X1)) (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq134 X1 (τ X0) (τ X0)
       have i₂ := eq168 X0
       grind)
    | exact superpose eq168 eq134
    | exact resolve eq134 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq444 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X2) (M.op X2 X3)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X1 X2
       have i₂ := eq106 X0 X1
       grind)
    | (have i₁ := eq23 X1 X1 X2
       have i₂ := eq106 X1 X1
       grind)
    | exact superpose eq106 eq23
    | (have j1 := eq106 X0 X1
       grind)
    | exact resolve eq23 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 X3) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 X0 X3 X4
       have i₂ := eq23 X0 X1 X2
       grind)
    | (have i₁ := eq23 X2 X1 X2
       have i₂ := eq23 X2 X2 X2
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X0 X3 (M.op X0 X0)
       have i₂ := eq23 X0 X1 X2
       grind)
    | (have i₁ := eq25 X1 X1 (M.op X1 X2)
       have i₂ := eq23 X1 X1 X2
       grind)
    | exact superpose eq23 eq25
    | exact resolve eq25 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X3 X3) X4)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X3 (M.op X0 X0) X4
       have i₂ := eq23 X0 X1 X2
       grind)
    | (have i₁ := eq25 X0 (M.op X2 X2) X2
       have i₂ := eq23 X2 X2 X2
       grind)
    | exact superpose eq23 eq25
    | exact resolve eq25 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq505 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op X0 X0)) (M.op (M.op X0 X1) (M.op X1 X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq23 X0 X1 X2
       grind)
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X1 X2)
       have i₂ := eq23 X0 X1 X2
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1710 : ∀ X0 X1 X2 : G, (σ (k X2 X0)) = (M.op (σ X0) (σ X2)) ∨ (σ (M.op X0 X1)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq103 X0 X1
       have i₂ := eq106 X0 X1
       grind)
    | (have i₁ := eq103 X1 X1
       have i₂ := eq106 X1 X1
       grind)
    | exact superpose eq106 eq103
    | (have j0 := eq103 X0 X2
       have j1 := eq106 X0 X1
       grind)
    | exact resolve eq103 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq3852 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op X0 (M.op X1 X1)) X1 x
       have i₂ := eq23 X0 (M.op X1 X1) x
       grind)
    | (have i₁ := eq175 (M.op (M.op X1 X1) (M.op X1 X1)) X1 (M.op X1 X1)
       have i₂ := eq23 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq23 eq175
    | exact resolve eq175 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq175
  have eq5766 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))) (M.op X0 X4)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq143 (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X1 x) (M.op x x)) X4
       have i₂ := eq505 X1 x x X0
       grind)
    | exact superpose eq505 eq143
    | exact resolve eq143 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq505
  have eq5791 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) X1) (M.op X0 X4)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq5766 X0 X1 X4
       have i₂ := eq3852 (M.op X0 X0) X1
       grind)
    | exact superpose eq3852 eq5766
    | exact resolve eq5766 eq3852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3852 eq5766
  have eq5824 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X0 X1) (M.op X0 X4)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq5791 X0 X1 X4
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq5791
    | exact resolve eq5791 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5791
  have eq7667 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq491 X1 X1 X1 X0
       have i₂ := eq5824 X0 (M.op X1 X1) X2
       grind)
    | (have i₁ := eq491 X0 X1 X2 (M.op X0 X1)
       have i₂ := eq5824 (M.op X0 X1) (M.op X0 X1) (M.op X1 X2)
       grind)
    | exact superpose eq5824 eq491
    | exact resolve eq491 eq5824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5824
  have eq8374 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X1)) X1 X2
       have i₂ := eq7667 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq7667 eq9
    | exact resolve eq9 eq7667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8764 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8374 X0 X1 X3
       have i₂ := eq8374 X0 X1 X2
       grind)
    | (have i₁ := eq8374 X0 X2 X2
       have i₂ := eq8374 X0 X2 X2
       grind)
    | exact superpose eq8374 eq8374
    | exact resolve eq8374 eq8374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8980 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X3)) X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7667 X0 X1 X3
       have i₂ := eq8374 X0 X1 X2
       grind)
    | (have i₁ := eq7667 X0 X2 X2
       have i₂ := eq8374 X0 X2 X2
       grind)
    | exact superpose eq8374 eq7667
    | exact resolve eq7667 eq8374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7667 eq8374
  have eq9256 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq256 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq256
    | exact resolve eq256 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq9557 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9256 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq9256
    | (have j0 := eq9256 X0 X1
       grind)
    | exact resolve eq9256 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9256
  have eq10173 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3)) X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq491 X1 X2 x X0
       have i₂ := eq8764 (M.op X0 X0) (M.op X1 X2) X3 (M.op X2 x)
       grind)
    | (have i₁ := eq491 X1 X2 x X0
       have i₂ := eq8764 (M.op X0 X0) (M.op X1 X2) (M.op X2 x) X3
       grind)
    | exact superpose eq8764 eq491
    | exact resolve eq491 eq8764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq10178 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op (M.op X1 X3) X4)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X0 (M.op X1 X3) X4
       have i₂ := eq8764 (M.op X0 X0) X1 X2 X3
       grind)
    | (have i₁ := eq9 X0 (M.op X1 X3) X4
       have i₂ := eq8764 (M.op X0 X0) X1 X3 X2
       grind)
    | exact superpose eq8764 eq9
    | exact resolve eq9 eq8764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8764
  have eq12740 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq272 X0 X1
       grind)
    | exact superpose eq272 eq10
    | (have j1 := eq272 X0 X1
       grind)
    | exact resolve eq10 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq12962 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12740 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq12740
    | (have j0 := eq12740 X0 X1
       grind)
    | exact resolve eq12740 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12740
  have eq14086 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10173 (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) X1 X2 X3
       have i₂ := eq8980 X0 (M.op (M.op X1 X2) X3) X4 (M.op (M.op (M.op X1 X2) X3) X4)
       grind)
    | exact superpose eq8980 eq10173
    | exact resolve eq10173 eq8980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10173
  have eq15070 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X5)) (M.op (M.op X1 X2) X3)) = X0 := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq8980 X0 (M.op (M.op X1 X2) X3) x X5
       have i₂ := eq14086 X0 X1 X2 X3 x
       grind)
    | exact superpose eq14086 eq8980
    | exact resolve eq8980 eq14086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8980 eq14086
  have eq15729 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq501 X0 X1 X1 X1 x
       have i₂ := eq454 (M.op X0 X1) (M.op X1 X1) x X2 X3
       grind)
    | (have i₁ := eq501 X0 X1 X1 X1 x
       have i₂ := eq454 (M.op X0 X1) X2 X3 (M.op X1 X1) x
       grind)
    | exact superpose eq454 eq501
    | exact resolve eq501 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq501
  have eq19669 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X0)) = (M.op (M.op (M.op (M.op (σ X0) X1) X2) (M.op X2 X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0
       have i₂ := eq15729 (σ X0) X1 X2 X3
       grind)
    | exact superpose eq15729 eq55
    | exact resolve eq55 eq15729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22766 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) (σ X1)
       have i₂ := eq353 X0 X1
       grind)
    | exact superpose eq353 eq84
    | (have j1 := eq353 X0 X1
       grind)
    | exact resolve eq84 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq22980 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq353 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq23009 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22766 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq22766
    | (have j0 := eq22766 X0 X1
       grind)
    | exact resolve eq22766 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22766
  have eq23063 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq23009 X0 X1
       have j1 := eq22980 X0 X1
       grind)
    | (have r₁ := eq23009 X0 X1
       have r₂ := eq22980 X0 X1
       grind)
    | exact resolve eq23009 eq22980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22980 eq23009
  have eq30755 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op (M.op X0 X1) (M.op X0 X1))) (τ X2)) (τ (M.op X2 X2))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq385 X2 (M.op X0 X0)
       have i₂ := eq444 X0 X1 X0 X0
       grind)
    | (have i₁ := eq385 X0 (M.op X0 X1)
       have i₂ := eq444 X0 X1 X2 x
       grind)
    | exact superpose eq444 eq385
    | (have j1 := eq444 X0 X1 X2 x
       grind)
    | exact resolve eq385 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq30913 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30755 X0 X1 x
       have i₂ := eq385 x (M.op X0 X1)
       grind)
    | exact superpose eq385 eq30755
    | (have j0 := eq30755 X0 X1 x
       grind)
    | exact resolve eq30755 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq30755
  have eq180005 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12962 y x
       grind)
    | exact superpose eq12962 eq16
    | (have j1 := eq12962 y x
       grind)
    | exact resolve eq16 eq12962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12962
  have eq180491 : (k y x) = (M.op y y) := by
    first
    | (have j1 := eq9557 x y
       grind)
    | (have r₁ := eq180005
       have r₂ := eq9557 x y
       grind)
    | exact resolve eq180005 eq9557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9557 eq180005
  have eq183926 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq106 x y
       have i₂ := eq180491
       grind)
    | exact superpose eq180491 eq106
    | (have j0 := eq106 x y
       grind)
    | exact resolve eq106 eq180491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq185117 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) (M.op X0 X1)) y) ∨ (M.op x y) = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq15729 y y x x
       have i₂ := eq183926
       grind)
    | exact superpose eq183926 eq15729
    | exact resolve eq15729 eq183926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183926
  have eq185131 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq185117 x x
       have i₂ := eq15729 x y x x
       grind)
    | exact superpose eq15729 eq185117
    | exact resolve eq185117 eq15729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15729 eq185117
  have eq185132 : (M.op x y) = (M.op x x) := by grind
  clear eq185131
  have eq222762 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (M.op X0 X1)) ∨ (σ (k X2 X0)) = (M.op (σ X0) (σ X2)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23063 X0 X2
       have i₂ := eq30913 X0 X1
       grind)
    | (have i₁ := eq23063 X1 X1
       have i₂ := eq30913 X1 X1
       grind)
    | exact superpose eq30913 eq23063
    | (have j0 := eq23063 X0 X2
       have j1 := eq30913 X0 X1
       grind)
    | exact resolve eq23063 eq30913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23063
  have eq423225 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x X0)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (M.op x X0)) ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1710 x X0 y
       grind)
    | exact superpose eq1710 eq16
    | (have j1 := eq1710 x X0 y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1710 x y y
       grind)
    | exact resolve eq16 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710
  have eq424574 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x X0)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq423225 X0
       have j1 := eq222762 x X0 y
       grind)
    | (have r₁ := eq423225 x
       have r₂ := eq222762 x x x
       grind)
    | exact resolve eq423225 eq222762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222762 eq423225
  have eq425578 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x X0)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq424574 X0
       have i₂ := eq185132
       grind)
    | exact superpose eq185132 eq424574
    | (have j0 := eq424574 X0
       grind)
    | exact resolve eq424574 eq185132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424574
  have eq426014 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq425578 X0
       have j1 := eq30913 x X0
       grind)
    | (have r₁ := eq425578 x
       have r₂ := eq30913 x x
       grind)
    | (have r₁ := eq425578 x
       have r₂ := eq30913 x x
       grind)
    | exact resolve eq425578 eq30913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30913 eq425578
  have eq426227 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq426014 X0
       have i₂ := eq180491
       grind)
    | exact superpose eq180491 eq426014
    | (have j0 := eq426014 X0
       grind)
    | exact resolve eq426014 eq180491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426014
  have eq426396 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq426227 X0
       grind)
    | exact superpose eq426227 eq16
    | (have j1 := eq426227 X0
       grind)
    | exact resolve eq16 eq426227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426418 : ∀ X0 X1 X2 : G, (σ (M.op x x)) = (M.op (M.op (M.op (σ (M.op y y)) X0) (M.op X0 X1)) (σ y)) ∨ (M.op x X2) = (k X2 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19669 x (σ y) X0 X1
       have i₂ := eq426227 X2
       grind)
    | exact superpose eq426227 eq19669
    | (have j1 := eq426227 X2
       grind)
    | exact resolve eq19669 eq426227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19669 eq426227
  have eq426875 : ∀ X2 : G, (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x X2) = (k X2 x) := by
    intro X2
    first
    | (have i₁ := eq426418 x x X2
       have i₂ := eq134 y x x
       grind)
    | exact superpose eq134 eq426418
    | (have j0 := eq426418 x x X2
       grind)
    | exact resolve eq426418 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq426418
  have eq426885 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq426396 X0
       have i₂ := eq185132
       grind)
    | exact superpose eq185132 eq426396
    | (have j0 := eq426396 X0
       grind)
    | exact resolve eq426396 eq185132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426396
  have eq426958 : ∀ X2 : G, (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x X2) = (k X2 x) := by
    intro X2
    first
    | (have i₁ := eq426875 X2
       have i₂ := eq55 y
       grind)
    | exact superpose eq55 eq426875
    | (have j0 := eq426875 X2
       grind)
    | exact resolve eq426875 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426875
  have eq426998 : ∀ X2 : G, (M.op x X2) = (k X2 x) := by
    intro X2
    first
    | (have j0 := eq426958 X2
       have j1 := eq426885 X2
       grind)
    | (have r₁ := eq426958 X2
       have r₂ := eq426885 x
       grind)
    | exact resolve eq426958 eq426885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426885 eq426958
  have eq432859 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq180491
       have i₂ := eq426998 y
       grind)
    | exact superpose eq426998 eq180491
    | exact resolve eq180491 eq426998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180491 eq426998
  have eq432862 : (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq432859
       have i₂ := eq185132
       grind)
    | exact superpose eq185132 eq432859
    | exact resolve eq432859 eq185132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185132 eq432859
  have eq436898 : ∀ X0 X1 X2 : G, y = (M.op (M.op (M.op x x) (M.op y X0)) (M.op (M.op y X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15070 y y X1 X2 X0
       have i₂ := eq432862
       grind)
    | exact superpose eq432862 eq15070
    | exact resolve eq15070 eq432862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15070 eq432862
  have eq436930 : x = y := by
    first
    | (have i₁ := eq436898 x x x
       have i₂ := eq10178 x y x x x
       grind)
    | exact superpose eq10178 eq436898
    | exact resolve eq436898 eq10178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10178 eq436898
  have eq438164 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq436930
       grind)
    | exact superpose eq436930 eq16
    | exact resolve eq16 eq436930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436930
  have eq438174 : False := by grind
  exact eq438174

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_x_pyx_Equation2045 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq26 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq46 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X2 X3)) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq46
    | (have j0 := eq46 X0 X1 x x
       grind)
    | exact resolve eq46 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq51 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 X0 X1
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq109 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (M.op (M.op X1 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X1 (σ X0) X2
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq26
    | exact resolve eq26 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq226 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq56
    | (have j0 := eq56 X0 X1
       have j1 := eq51 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq56 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq56
  have eq5436 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq226 x y
       grind)
    | exact superpose eq226 eq16
    | (have j1 := eq226 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq226 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq226 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq226 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq5513 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5436
  have eq5862 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ (M.op x x)) (M.op (M.op X0 X0) X1)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq109 y X0 X1
       have i₂ := eq5513
       grind)
    | exact superpose eq5513 eq109
    | exact resolve eq109 eq5513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5513
  have eq5892 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5862 x x
       have i₂ := eq109 x x x
       grind)
    | exact superpose eq109 eq5862
    | exact resolve eq5862 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq5862
  have eq5893 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq5892
  have eq8240 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5893
       grind)
    | exact superpose eq5893 eq10
    | exact resolve eq10 eq5893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5893
  have eq8270 : x = y ∨ x = y := by
    first
    | (have i₁ := eq8240
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8240
    | exact resolve eq8240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8240
  have eq8271 : x = y := by grind
  clear eq8270
  have eq12980 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8271
       grind)
    | exact superpose eq8271 eq16
    | exact resolve eq16 eq8271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8271
  have eq12981 : False := by grind
  exact eq12981

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyy_pxx_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
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
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y
       grind)
    | exact resolve eq15 eq24
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
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq178 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq662 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq662 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq662 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq662 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq662 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq669 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq663 X0
       grind)
    | exact superpose eq663 eq16
    | exact resolve eq16 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq663 X0
       grind)
    | exact superpose eq663 eq16
    | exact resolve eq16 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 (M.op X0 X0)
       have i₂ := eq663 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq663 eq16
    | exact resolve eq16 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : ∀ X0 : G, (k (M.op (k X0 X0) X0) (M.op (k X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq672 X0
       have i₂ := eq663 X0
       grind)
    | exact superpose eq663 eq672
    | exact resolve eq672 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq1222 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq657
       grind)
    | exact superpose eq657 eq40
    | exact resolve eq40 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq1223 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1222
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1222
    | exact resolve eq1222 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222
  have eq1225 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1223
    | exact resolve eq1223 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1227 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1225
       have i₂ := eq663 y
       grind)
    | exact superpose eq663 eq1225
    | exact resolve eq1225 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1260 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 (k X0 X0) X1
       have i₂ := eq669 X0 X0 (k X0 X0)
       grind)
    | exact superpose eq669 eq178
    | exact resolve eq178 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq669
  have eq2444 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq1227 eq658
    | exact resolve eq658 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq1227
  have eq2451 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have r₁ := eq2444
       have r₂ := eq27
       grind)
    | exact resolve eq2444 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2444
  have eq2455 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq2451
       have i₂ := eq663 sF3
       grind)
    | exact superpose eq663 eq2451
    | exact resolve eq2451 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2451
  have eq2460 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq2455 eq115
    | exact resolve eq115 eq2455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq2455
  have eq2482 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq29 eq2460
    | exact resolve eq2460 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460
  have eq2483 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2482
  have eq2496 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq2483
       grind)
    | exact superpose eq2483 eq40
    | exact resolve eq40 eq2483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq2504 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq701 y
       have i₂ := eq2483
       grind)
    | exact superpose eq2483 eq701
    | exact resolve eq701 eq2483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701 eq2483
  have eq2511 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2504
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2504
    | exact resolve eq2504 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2504
  have eq2514 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2496
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2496
    | exact resolve eq2496 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2496
  have eq2520 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2514
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2514
    | exact resolve eq2514 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2514
  have eq3091 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2511 eq41
    | exact resolve eq41 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq2511
  have eq3109 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq3091
    | exact resolve eq3091 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3091
  have eq3115 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3109
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3109
    | exact resolve eq3109 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3109
  have eq3975 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3115 eq670
    | exact resolve eq670 eq3115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq3115
  have eq3986 : (σ (M.op x y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3975 x
       have i₂ := eq1260 sF3 x
       grind)
    | exact superpose eq1260 eq3975
    | exact resolve eq3975 eq1260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260 eq3975
  have eq3992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2520 eq3986
    | exact resolve eq3986 eq2520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2520 eq3986
  have eq3996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq3992
    | exact resolve eq3992 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992
  have eq3998 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq3996
       have r₂ := eq27
       grind)
    | exact resolve eq3996 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3996
  have eq4001 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq3998 eq31
    | exact resolve eq31 eq3998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3998
  have eq4041 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq4001
    | exact resolve eq4001 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4001
  have eq4042 : x = y := by grind
  clear eq4041
  have eq4047 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4042
       grind)
    | exact superpose eq4042 eq18
    | exact resolve eq18 eq4042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4048 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4042
       grind)
    | exact superpose eq4042 eq24
    | exact resolve eq24 eq4042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4042
  have eq4072 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4048
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4048
    | exact resolve eq4048 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4048
  have eq4073 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq4047
       have i₂ := eq663 x
       grind)
    | exact superpose eq663 eq4047
    | exact resolve eq4047 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4047
  have eq4080 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4072 eq26
    | exact resolve eq26 eq4072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4072
  have eq4122 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4080
       have i₂ := eq663 sF2
       grind)
    | exact superpose eq663 eq4080
    | exact resolve eq4080 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq4080
  have eq4134 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq4073
       grind)
    | exact superpose eq4073 eq39
    | exact resolve eq39 eq4073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq4073
  have eq4150 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4134
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4134
    | exact resolve eq4134 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4134
  have eq4154 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4122 eq4150
    | exact resolve eq4150 eq4122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4122 eq4150
  have eq4156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4154
    | exact resolve eq4154 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4154
  have eq4158 : False := by grind
  exact eq4158
