import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_pxx_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq32 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq32 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq32 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq43 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq34 X1 X0
       grind)
    | (have r₁ := eq43 X0 X1
       have r₂ := eq34 (k X0 X1) (M.op X0 X0)
       grind)
    | (have r₁ := eq43 X0 X1
       have r₂ := eq34 (M.op X0 X0) (k X0 X1)
       grind)
    | (have r₁ := eq43 X0 X1
       have r₂ := eq34 X0 X1
       grind)
    | exact resolve eq43 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq43
  have eq58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq56 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq75 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq97 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq75 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq75 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq175 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq177 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq175 X0 X1
       have j1 := eq97 X0 X1
       grind)
    | (have r₁ := eq175 X0 X1
       have r₂ := eq97 X0 X1
       grind)
    | (have r₁ := eq175 X1 X1
       have r₂ := eq97 X1 X1
       grind)
    | exact resolve eq175 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq175
  have eq519 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq177 (σ X1) (σ X0)
       grind)
    | exact superpose eq177 eq15
    | exact resolve eq15 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq519 X0 X1
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq519
    | exact resolve eq519 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq519
  have eq527 : False := by grind
  exact eq527

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq34
    | (have j0 := eq34 X0 X1
       grind)
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq43 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq31
    | (have j0 := eq31 X0 X1
       grind)
    | exact resolve eq31 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq69 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq69
    | exact resolve eq69 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq72
    | exact resolve eq72 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq169 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq43
    | (have j0 := eq43 X0 X1
       have j1 := eq40 (σ (M.op X0 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq43 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq43
  have eq1894 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq169 x y
       grind)
    | exact superpose eq169 eq16
    | (have j1 := eq169 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq169 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq169 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq169 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq1925 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1894
  have eq4089 : (σ y) = (M.op (σ x) (M.op (σ (M.op x x)) (σ (M.op x x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq1925
       grind)
    | exact superpose eq1925 eq9
    | exact resolve eq9 eq1925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925
  have eq4119 : (σ y) = (M.op (σ x) (σ (M.op (M.op x x) (M.op x x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4089
       have i₂ := eq22 (M.op x x)
       grind)
    | exact superpose eq22 eq4089
    | exact resolve eq4089 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4089
  have eq4126 : (σ y) = (M.op (σ x) (σ (M.op x (M.op x x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4119
       have i₂ := eq24 x x
       grind)
    | exact superpose eq24 eq4119
    | exact resolve eq4119 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4119
  have eq4129 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4126
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq4126
    | exact resolve eq4126 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq4126
  have eq4130 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq4129
  have eq7079 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4130
       grind)
    | exact superpose eq4130 eq10
    | exact resolve eq10 eq4130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4130
  have eq7127 : x = y ∨ x = y := by
    first
    | (have i₁ := eq7079
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7079
    | exact resolve eq7079 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7079
  have eq7128 : x = y := by grind
  clear eq7127
  have eq10398 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7128
       grind)
    | exact superpose eq7128 eq16
    | exact resolve eq16 eq7128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7128
  have eq10399 : False := by grind
  exact eq10399

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pyy_pxy_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq31 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq31
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq65 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq67 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq66
    | (have j0 := eq66 X0
       grind)
    | exact resolve eq66 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq68 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq65
    | exact resolve eq65 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq75 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq10
    | exact resolve eq10 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq98 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq118 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq109 x y
       grind)
    | exact superpose eq109 eq16
    | (have j1 := eq109 x y
       grind)
    | exact resolve eq16 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (M.op (σ (k X0 X1)) (σ (k X0 X1)))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X1) (σ X0)
       have i₂ := eq109 X0 X1
       grind)
    | exact superpose eq109 eq9
    | (have j1 := eq109 X0 X1
       grind)
    | exact resolve eq9 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq121 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ (M.op (k X0 X1) (k X0 X1)))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0 X1
       have i₂ := eq23 (k X0 X1)
       grind)
    | exact superpose eq23 eq120
    | (have j0 := eq120 X0 X1
       grind)
    | exact resolve eq120 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq297 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X1 (τ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq98
    | exact resolve eq98 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq305 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq98 (τ (M.op X0 X0)) (τ (M.op X0 X0))
       have i₂ := eq297 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq297 eq98
    | exact resolve eq98 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq297
  have eq404 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq305 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq305
    | exact resolve eq305 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq412 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (M.op (τ (σ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq404 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq404
    | exact resolve eq404 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq415 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq412 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq412
    | exact resolve eq412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq458 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq415 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq415
    | exact resolve eq415 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq118
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq118
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq118
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq118
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq118 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq613 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq612
  have eq712 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq68
    | exact resolve eq68 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1840 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k (M.op X0 X0) X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq10
    | (have j1 := eq67 X0
       grind)
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1874 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1840 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1840
    | (have j0 := eq1840 X0
       grind)
    | exact resolve eq1840 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840
  have eq2192 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (M.op (σ (M.op (k X1 X0) (k X1 X0))) (σ (M.op (k X1 X0) (k X1 X0))))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ (M.op (k X0 X1) (k X0 X1))) (σ X0)
       have i₂ := eq121 X0 X1
       grind)
    | exact superpose eq121 eq25
    | (have j1 := eq121 X1 X0
       grind)
    | exact resolve eq25 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq2195 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ (M.op (M.op (k X1 X0) (k X1 X0)) (M.op (k X1 X0) (k X1 X0))))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2192 X0 X1
       have i₂ := eq23 (M.op (k X1 X0) (k X1 X0))
       grind)
    | exact superpose eq23 eq2192
    | (have j0 := eq2192 X0 X1
       grind)
    | exact resolve eq2192 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2192
  have eq2216 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ (M.op (k X1 X0) (M.op (k X1 X0) (k X1 X0))))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2195 X0 X1
       have i₂ := eq25 (k X1 X0) (k X1 X0)
       grind)
    | exact superpose eq25 eq2195
    | (have j0 := eq2195 X0 X1
       grind)
    | exact resolve eq2195 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2195
  have eq2231 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ (M.op (k X1 X0) (M.op (k X1 X0) (k X1 X0))))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2216 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq2216
    | (have j0 := eq2216 X0 X1
       grind)
    | exact resolve eq2216 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216
  have eq6533 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq613
       grind)
    | exact superpose eq613 eq16
    | exact resolve eq16 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq6534 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq6533
       have r₂ := eq23 x
       grind)
    | exact resolve eq6533 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6533
  have eq229699 : x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1874 y
       have i₂ := eq6534
       grind)
    | exact superpose eq6534 eq1874
    | exact resolve eq1874 eq6534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874 eq6534
  have eq229831 : x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq229699
  have eq2721901 : (σ (M.op y y)) = (M.op (σ x) (σ (M.op x (M.op x x)))) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2231 y x
       have i₂ := eq229831
       grind)
    | exact superpose eq229831 eq2231
    | (have j0 := eq2231 y x
       grind)
    | exact resolve eq2231 eq229831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231 eq229831
  have eq2722048 : (σ (M.op y y)) = (M.op (σ x) (σ (M.op x (M.op x x)))) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq2721901
  have eq2722078 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2722048
       have i₂ := eq712 x
       grind)
    | exact superpose eq712 eq2722048
    | exact resolve eq2722048 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq2722048
  have eq2722079 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq2722078
  have eq2722102 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2722079
       grind)
    | exact superpose eq2722079 eq10
    | exact resolve eq10 eq2722079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2722079
  have eq2723179 : x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2722102
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2722102
    | exact resolve eq2722102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2722102
  have eq2723209 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2723179
       grind)
    | exact superpose eq2723179 eq16
    | exact resolve eq16 eq2723179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723179
  have eq2723210 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq2723209
       have r₂ := eq23 x
       grind)
    | exact resolve eq2723209 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2723209
  have eq2723244 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq458 y
       have i₂ := eq2723210
       grind)
    | exact superpose eq2723210 eq458
    | exact resolve eq458 eq2723210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq2723380 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2723210
       grind)
    | exact superpose eq2723210 eq10
    | exact resolve eq10 eq2723210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723210
  have eq2724719 : x = (M.op y y) := by
    first
    | (have i₁ := eq2723380
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2723380
    | exact resolve eq2723380 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723380
  have eq2724905 : x = (M.op x y) := by
    first
    | (have i₁ := eq415 y
       have i₂ := eq2724719
       grind)
    | exact superpose eq2724719 eq415
    | exact resolve eq415 eq2724719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq2724719
  have eq2950819 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2723244
       grind)
    | exact superpose eq2723244 eq16
    | exact resolve eq16 eq2723244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723244
  have eq2951384 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2950819
       have i₂ := eq2724905
       grind)
    | exact superpose eq2724905 eq2950819
    | exact resolve eq2950819 eq2724905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724905 eq2950819
  have eq2951385 : False := by grind
  exact eq2951385

/-- `Equation916`: `x = y ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_x_x_pyx_Equation916 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law916 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law916.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (k (M.op X1 X1) X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
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
  have eq32 : y = (τ (σ y)) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq44 : ∀ X0 X1 : G, (σ (k (k x X0) X1)) = (k (k (σ x) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k x X0) X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq10
    | exact resolve eq10 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq28 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (σ (M.op x x)) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq40 (M.op x x)
       have i₂ := eq176 x
       grind)
    | exact superpose eq176 eq40
    | exact resolve eq40 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (σ (M.op y y)) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq41 (M.op y y)
       have i₂ := eq176 y
       grind)
    | exact superpose eq176 eq41
    | exact resolve eq41 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq204 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq193
    | exact resolve eq193 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq211 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq222 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq211
    | exact resolve eq211 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq246 : (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq142 (M.op sF2 sF2)
       have i₂ := eq176 sF2
       grind)
    | exact superpose eq176 eq142
    | exact resolve eq142 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq267 : (τ (M.op (σ y) (σ y))) = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | (have i₁ := eq153 (M.op sF3 sF3)
       have i₂ := eq176 sF3
       grind)
    | exact superpose eq176 eq153
    | exact resolve eq153 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq697 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq16 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq749 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (k (M.op (M.op X0 X0) (M.op X1 X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq11 (M.op (M.op X0 X0) (M.op X1 X1)) X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq768 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq790 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq743 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq824 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq769 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq769
    | (have j0 := eq769 (σ X0)
       grind)
    | exact resolve eq769 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq697 (M.op X0 X0)
       have i₂ := eq697 X0
       grind)
    | exact superpose eq697 eq697
    | exact resolve eq697 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq932 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0
       have i₂ := eq697 X0
       grind)
    | exact superpose eq697 eq16
    | exact resolve eq16 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq934 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq697 X0
       grind)
    | exact superpose eq697 eq16
    | exact resolve eq16 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X1
       have i₂ := eq697 X0
       grind)
    | exact superpose eq697 eq16
    | exact resolve eq16 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq937 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq175 (M.op X0 X0)
       have i₂ := eq697 X0
       grind)
    | exact superpose eq697 eq175
    | exact resolve eq175 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq938 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq176 (M.op X0 X0)
       have i₂ := eq697 X0
       grind)
    | exact superpose eq697 eq176
    | exact resolve eq176 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq944 : ∀ X0 : G, (M.op X0 (M.op X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq932 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq932
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq932 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : ∀ X0 : G, (M.op X0 (M.op X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq944 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq951 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (M.op X0 (k X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq937 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq937
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq937 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq953 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (M.op X0 (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq951 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq1510 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq756
       grind)
    | exact superpose eq756 eq40
    | exact resolve eq40 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1511 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1510
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1510
    | exact resolve eq1510 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510
  have eq1513 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1511
    | exact resolve eq1511 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq7790 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (k X1 X1))) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq790 X1 (M.op X0 X0)
       have i₂ := eq697 X0
       grind)
    | exact superpose eq697 eq790
    | (have j0 := eq790 X1 X1
       grind)
    | exact resolve eq790 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7791 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 X1) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq790 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq790
    | (have j0 := eq790 (σ X0) X1
       grind)
    | exact resolve eq790 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq17252 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq935 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq934 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq934 eq935
    | exact resolve eq935 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17253 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq935 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq16 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact superpose eq16 eq935
    | exact resolve eq935 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq17263 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq17253 X0
       have i₂ := eq16 X0 X0
       grind)
    | exact superpose eq16 eq17253
    | exact resolve eq17253 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17253
  have eq17264 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq17252 X0
       have i₂ := eq932 X0
       grind)
    | exact superpose eq932 eq17252
    | exact resolve eq17252 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17252
  have eq17268 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq17263 X0
       have i₂ := eq697 (M.op X0 X0)
       grind)
    | exact superpose eq697 eq17263
    | exact resolve eq17263 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17263
  have eq17270 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq17268 X0
       have i₂ := eq697 X0
       grind)
    | exact superpose eq697 eq17268
    | exact resolve eq17268 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17268
  have eq17272 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq17270 (M.op X0 X0)
       have i₂ := eq697 X0
       grind)
    | exact superpose eq697 eq17270
    | exact resolve eq17270 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17278 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq17272 X0
       have i₂ := eq17270 X0
       grind)
    | exact superpose eq17270 eq17272
    | exact resolve eq17272 eq17270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17272
  have eq17295 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq749 X0 (M.op X0 X0)
       have i₂ := eq17264 (M.op X0 X0)
       grind)
    | exact superpose eq17264 eq749
    | (have j0 := eq749 X0 (M.op X0 X0)
       grind)
    | exact resolve eq749 eq17264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq17297 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq17264 X0
       grind)
    | exact superpose eq17264 eq16
    | exact resolve eq16 eq17264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17298 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq17264 X0
       grind)
    | exact superpose eq17264 eq16
    | exact resolve eq16 eq17264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17301 : ∀ X0 : G, (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 (M.op X0 (M.op X0 X0))
       have i₂ := eq17264 X0
       grind)
    | exact superpose eq17264 eq176
    | exact resolve eq176 eq17264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17310 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq934 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq17264 X0
       grind)
    | exact superpose eq17264 eq934
    | exact resolve eq934 eq17264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17330 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq17295 X0
       have i₂ := eq697 X0
       grind)
    | exact superpose eq697 eq17295
    | (have j0 := eq17295 X0
       grind)
    | exact resolve eq17295 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17295
  have eq17335 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq17330 X0
       have i₂ := eq17270 X0
       grind)
    | exact superpose eq17270 eq17330
    | (have j0 := eq17330 X0
       grind)
    | exact resolve eq17330 eq17270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17330
  have eq17336 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have j0 := eq17335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17335
  have eq17341 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17336 X0
       have i₂ := eq697 X0
       grind)
    | exact superpose eq697 eq17336
    | (have j0 := eq17336 X0
       grind)
    | exact resolve eq17336 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17336
  have eq17343 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17341 X0
       have i₂ := eq17270 X0
       grind)
    | exact superpose eq17270 eq17341
    | (have j0 := eq17341 X0
       grind)
    | exact resolve eq17341 eq17270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17341
  have eq17381 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq38 (M.op sF0 (M.op sF0 sF0))
       have i₂ := eq17301 sF0
       grind)
    | exact superpose eq17301 eq38
    | exact resolve eq38 eq17301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17389 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq20 eq17381
    | exact resolve eq17381 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17381
  have eq17747 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17297 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq17297 X0 X0
       grind)
    | exact superpose eq17297 eq17297
    | exact resolve eq17297 eq17297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17856 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq932 X1
       have i₂ := eq17298 X1 X0
       grind)
    | exact superpose eq17298 eq932
    | exact resolve eq932 eq17298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17862 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17270 X1
       have i₂ := eq17298 X1 X0
       grind)
    | exact superpose eq17298 eq17270
    | exact resolve eq17270 eq17298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17863 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17278 X1
       have i₂ := eq17298 X1 X0
       grind)
    | exact superpose eq17298 eq17278
    | exact resolve eq17278 eq17298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17865 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17301 X1
       have i₂ := eq17298 X1 X0
       grind)
    | exact superpose eq17298 eq17301
    | exact resolve eq17301 eq17298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17301
  have eq17908 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17856 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq17297 X0 X0
       grind)
    | exact superpose eq17297 eq17856
    | exact resolve eq17856 eq17297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17927 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq17856 x (M.op X0 X0)
       have i₂ := eq16 X0 x
       grind)
    | exact superpose eq16 eq17856
    | exact resolve eq17856 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17984 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17865 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq17297 X0 X0
       grind)
    | exact superpose eq17297 eq17865
    | exact resolve eq17865 eq17297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19032 : y = (M.op y (M.op (M.op x (M.op x x)) (M.op x y))) := by
    first
    | (have i₁ := eq17908 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17908
    | (have j0 := eq17908 x y
       grind)
    | exact resolve eq17908 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19033 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq17908
    | (have j0 := eq17908 (σ x) (σ y)
       grind)
    | exact resolve eq17908 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19350 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1513 eq764
    | exact resolve eq764 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513
  have eq19357 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq19350
       have r₂ := eq27
       grind)
    | exact resolve eq19350 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19350
  have eq19367 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19357 eq246
    | exact resolve eq246 eq19357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19368 : x = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19357 eq204
    | exact resolve eq204 eq19357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq19357
  have eq19437 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq19368
    | exact resolve eq19368 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19368
  have eq19438 : y = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq19367
    | exact resolve eq19367 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19367
  have eq19443 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq19437
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq19437
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq19437
       have r₂ := eq13 y x
       grind)
    | exact resolve eq19437 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19437
  have eq19444 : y = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq19438
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq19438
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq19438
       have r₂ := eq13 y x
       grind)
    | exact resolve eq19438 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19438
  have eq19448 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by
    first
    | (have j1 := eq28 x y
       grind)
    | (have r₁ := eq19443
       have r₂ := eq28 (σ x) (σ y)
       grind)
    | (have r₁ := eq19443
       have r₂ := eq28 x y
       grind)
    | exact resolve eq19443 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19443
  have eq19449 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | (have j1 := eq28 y x
       grind)
    | (have r₁ := eq19444
       have r₂ := eq28 (σ x) (σ y)
       grind)
    | (have r₁ := eq19444
       have r₂ := eq28 y x
       grind)
    | exact resolve eq19444 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq19444
  have eq19453 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (k x y) := by
    first
    | exact superpose eq19448 eq267
    | exact resolve eq267 eq19448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19448
  have eq19504 : x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq30 eq19453
    | exact resolve eq19453 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19453
  have eq19505 : x = (k x y) := by grind
  clear eq19504
  have eq19513 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq19505
       grind)
    | exact superpose eq19505 eq41
    | exact resolve eq41 eq19505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19505
  have eq19514 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq19513
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19513
    | exact resolve eq19513 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19513
  have eq19543 : y = (k y (τ (σ x))) ∨ y = (k y x) := by
    first
    | exact superpose eq19449 eq222
    | exact resolve eq222 eq19449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq19449
  have eq19592 : y = (k y x) ∨ y = (k y x) := by
    first
    | exact superpose eq30 eq19543
    | exact resolve eq19543 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19543
  have eq19593 : y = (k y x) := by grind
  clear eq19592
  have eq19602 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq756
       have i₂ := eq19593
       grind)
    | exact superpose eq19593 eq756
    | exact resolve eq756 eq19593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq19604 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq19593
       grind)
    | exact superpose eq19593 eq40
    | exact resolve eq40 eq19593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19593
  have eq19605 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq19604
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19604
    | exact resolve eq19604 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19604
  have eq19615 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq19605 eq764
    | exact resolve eq764 eq19605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq19605
  have eq19925 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq697 x
       have i₂ := eq19602
       grind)
    | exact superpose eq19602 eq697
    | exact resolve eq697 eq19602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19932 : x = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq932 x
       have i₂ := eq19602
       grind)
    | exact superpose eq19602 eq932
    | exact resolve eq932 eq19602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19942 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17270 x
       have i₂ := eq19602
       grind)
    | exact superpose eq19602 eq17270
    | exact resolve eq17270 eq19602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19944 : ∀ X0 : G, x = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq17297 X0 x
       have i₂ := eq19602
       grind)
    | exact superpose eq19602 eq17297
    | exact resolve eq17297 eq19602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19960 : y = (k x x) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq19602
       grind)
    | exact superpose eq19602 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq19602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19602
  have eq19961 : y = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq19960
  have eq19971 : x = (M.op y (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19944 x
       have i₂ := eq17747 y x
       grind)
    | exact superpose eq17747 eq19944
    | exact resolve eq19944 eq17747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19944
  have eq19973 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19942
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19942
    | exact resolve eq19942 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19942
  have eq19982 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq19932
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19932
    | exact resolve eq19932 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19932
  have eq19985 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19925
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19925
    | exact resolve eq19925 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19925
  have eq20100 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq19615 eq697
    | exact resolve eq697 eq19615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20107 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq19615 eq932
    | exact resolve eq932 eq19615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20135 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq19615 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq19615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19615
  have eq20136 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq20135
  have eq20157 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq20107
    | exact resolve eq20107 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20107
  have eq20160 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq20100
    | exact resolve eq20100 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20100
  have eq20364 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq17927 y
       have i₂ := eq19982
       grind)
    | exact superpose eq19982 eq17927
    | exact resolve eq17927 eq19982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19982
  have eq20371 : x = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20364
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20364
    | exact resolve eq20364 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20364
  have eq20394 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x (M.op x x)) x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20371 eq17908
    | exact resolve eq17908 eq20371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20371
  have eq20396 : (M.op x y) = (M.op (M.op x y) (M.op x x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20394
       have i₂ := eq17278 x
       grind)
    | exact superpose eq17278 eq20394
    | exact resolve eq20394 eq17278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20394
  have eq20445 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq19985
       grind)
    | exact superpose eq19985 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq19985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20447 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq20445
  have eq21292 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20157 eq17927
    | exact resolve eq17927 eq20157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20157
  have eq21299 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21292
    | exact resolve eq21292 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21292
  have eq21312 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21299 eq17908
    | exact resolve eq17908 eq21299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21299
  have eq21314 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21312
       have i₂ := eq17278 sF2
       grind)
    | exact superpose eq17278 eq21312
    | exact resolve eq21312 eq17278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21312
  have eq21366 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20160 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq20160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21367 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq20160
  have eq21368 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq21366
  have eq21453 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq20447
       grind)
    | exact superpose eq20447 eq41
    | exact resolve eq41 eq20447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20447
  have eq21471 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq21453
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21453
    | exact resolve eq21453 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21453
  have eq21478 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq21471
    | exact resolve eq21471 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21471
  have eq21487 : x = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20396 eq17297
    | exact resolve eq17297 eq20396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21496 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21487
       have i₂ := eq17278 sF0
       grind)
    | exact superpose eq17278 eq21487
    | exact resolve eq21487 eq17278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21487
  have eq21504 : ∀ X0 : G, (M.op (M.op x y) (M.op x (M.op X0 X0))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21496 eq16
    | exact resolve eq16 eq21496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21509 : (M.op x x) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21496 eq697
    | exact resolve eq697 eq21496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21527 : (M.op x y) = (M.op x (M.op (M.op x y) x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21496 eq17270
    | exact resolve eq17270 eq21496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17270
  have eq21724 : (M.op (M.op x y) (M.op y (M.op x y))) = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq930 y
       have i₂ := eq19985
       grind)
    | exact superpose eq19985 eq930
    | exact resolve eq930 eq19985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq21853 : (M.op x x) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19973 eq21724
    | exact resolve eq21724 eq19973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19973 eq21724
  have eq21900 : (M.op x x) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21509 eq21853
    | exact resolve eq21853 eq21509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21853
  have eq22286 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21314 eq17297
    | exact resolve eq17297 eq21314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21314
  have eq22295 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22286
       have i₂ := eq17278 sF4
       grind)
    | exact superpose eq17278 eq22286
    | exact resolve eq22286 eq17278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22286
  have eq22327 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq22295 eq17297
    | exact resolve eq17297 eq22295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22348 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22327 x
       have i₂ := eq17747 sF2 x
       grind)
    | exact superpose eq17747 eq22327
    | exact resolve eq22327 eq17747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22327
  have eq22401 : y = (M.op y (M.op (M.op x (M.op (M.op x y) x)) (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19032
       have i₂ := eq21509
       grind)
    | exact superpose eq21509 eq19032
    | exact resolve eq19032 eq21509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21509
  have eq22486 : y = (M.op y (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21527 eq22401
    | exact resolve eq22401 eq21527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21527 eq22401
  have eq22496 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21496 eq22486
    | exact resolve eq22486 eq21496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22486
  have eq22500 : x = (k x (M.op (M.op y (M.op y y)) y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17984 y x
       have i₂ := eq22496
       grind)
    | exact superpose eq22496 eq17984
    | exact resolve eq17984 eq22496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17984
  have eq22501 : x = (M.op x (M.op (M.op y (M.op y y)) y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17908 y x
       have i₂ := eq22496
       grind)
    | exact superpose eq22496 eq17908
    | exact resolve eq17908 eq22496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22496
  have eq22504 : x = (M.op x (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22501
       have i₂ := eq17278 y
       grind)
    | exact superpose eq17278 eq22501
    | exact resolve eq22501 eq17278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22501
  have eq22505 : x = (k x (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22500
       have i₂ := eq17278 y
       grind)
    | exact superpose eq17278 eq22500
    | exact resolve eq22500 eq17278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22500
  have eq23322 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22348 eq19033
    | exact resolve eq19033 eq22348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23353 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22295 eq23322
    | exact resolve eq23322 eq22295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22295 eq23322
  have eq23371 : (σ x) = (M.op (σ x) (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23353 eq17908
    | exact resolve eq17908 eq23353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23353
  have eq23374 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23371
       have i₂ := eq17278 sF3
       grind)
    | exact superpose eq17278 eq23371
    | exact resolve eq23371 eq17278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23371
  have eq23401 : y = (M.op (M.op x (M.op x x)) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17297 x y
       have i₂ := eq22504
       grind)
    | exact superpose eq22504 eq17297
    | exact resolve eq17297 eq22504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22504
  have eq23411 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23401
       have i₂ := eq17278 x
       grind)
    | exact superpose eq17278 eq23401
    | exact resolve eq23401 eq17278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23401
  have eq23442 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq697 x
       have i₂ := eq23411
       grind)
    | exact superpose eq23411 eq697
    | exact resolve eq697 eq23411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23453 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq934 x x
       have i₂ := eq23411
       grind)
    | exact superpose eq23411 eq934
    | exact resolve eq934 eq23411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq23481 : y = (k x x) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq23411
       grind)
    | exact superpose eq23411 eq11
    | exact resolve eq11 eq23411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23411
  have eq23482 : y = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23481
  have eq23510 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23453 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23453
    | (have j0 := eq23453 X0
       grind)
    | exact resolve eq23453 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23453
  have eq23517 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23442
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23442
    | exact resolve eq23442 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23442
  have eq23654 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq23517
       grind)
    | exact superpose eq23517 eq11
    | exact resolve eq11 eq23517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23655 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23654
  have eq24044 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq23655
       grind)
    | exact superpose eq23655 eq41
    | exact resolve eq41 eq23655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24072 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24044
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24044
    | exact resolve eq24044 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24044
  have eq24083 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq24072
    | exact resolve eq24072 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24072
  have eq24555 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23374 eq17297
    | exact resolve eq17297 eq23374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23374
  have eq24565 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24555
       have i₂ := eq17278 sF2
       grind)
    | exact superpose eq17278 eq24555
    | exact resolve eq24555 eq17278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24555
  have eq24585 : ∀ X0 : G, (σ y) ≠ X0 ∨ (σ x) = (k (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24565 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq24565
       grind)
    | exact resolve eq13 eq24565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24591 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24565 eq697
    | exact resolve eq697 eq24565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24631 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24565 eq11
    | exact resolve eq11 eq24565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24632 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24631
  have eq24663 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq24591
    | exact resolve eq24591 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24591
  have eq24777 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24663 eq11
    | exact resolve eq11 eq24663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24778 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24777
  have eq24826 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24778 eq116
    | exact resolve eq116 eq24778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24833 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24778 eq21478
    | exact resolve eq21478 eq24778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21478
  have eq24834 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24778 eq24083
    | exact resolve eq24083 eq24778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24083 eq24778
  have eq24866 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq24834
       have r₂ := eq27
       grind)
    | exact resolve eq24834 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24834
  have eq24867 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq24833
       have r₂ := eq27
       grind)
    | exact resolve eq24833 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24833
  have eq24872 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24866 eq24867
    | exact resolve eq24867 eq24866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24866 eq24867
  have eq26486 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq23482
       grind)
    | exact superpose eq23482 eq40
    | exact resolve eq40 eq23482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23482
  have eq26514 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26486
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26486
    | exact resolve eq26486 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26486
  have eq26523 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26514
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26514
    | exact resolve eq26514 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26514
  have eq26650 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24632 eq98
    | exact resolve eq98 eq24632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26678 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq26650
    | exact resolve eq26650 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26650
  have eq27272 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq24872
       grind)
    | exact superpose eq24872 eq11
    | exact resolve eq11 eq24872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24872
  have eq27273 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27272
  have eq27325 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq27273
       grind)
    | exact superpose eq27273 eq41
    | exact resolve eq41 eq27273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27273
  have eq27357 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27325
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27325
    | exact resolve eq27325 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27325
  have eq27367 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq27357
    | exact resolve eq27357 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27357
  have eq27500 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27367 eq21368
    | exact resolve eq21368 eq27367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21368 eq27367
  have eq27525 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27500
  have eq27528 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq27525
       have r₂ := eq21367
       grind)
    | exact resolve eq27525 eq21367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21367 eq27525
  have eq27531 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq27528
       have r₂ := eq27
       grind)
    | exact resolve eq27528 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27528
  have eq27578 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27531 eq17264
    | exact resolve eq17264 eq27531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27599 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27531 eq11
    | exact resolve eq11 eq27531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27600 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq27599
  have eq28285 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27600 eq116
    | exact resolve eq116 eq27600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27600
  have eq28339 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq28285
    | exact resolve eq28285 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28285
  have eq28381 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23655
       have i₂ := eq28339
       grind)
    | exact superpose eq28339 eq23655
    | exact resolve eq23655 eq28339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23655 eq28339
  have eq28409 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq28381
  have eq28556 : x = (k x (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq938 y
       have i₂ := eq19971
       grind)
    | exact superpose eq19971 eq938
    | exact resolve eq938 eq19971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938 eq19971
  have eq28583 : x = (k x (M.op y y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq22505 eq28556
    | exact resolve eq28556 eq22505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22505 eq28556
  have eq28591 : (M.op x y) = (k (M.op x y) (M.op y y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq23517 eq28583
    | exact resolve eq28583 eq23517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28583
  have eq28594 : (M.op x y) = (k (M.op x y) x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq19985 eq28591
    | exact resolve eq28591 eq19985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19985 eq28591
  have eq28596 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq23517 eq28594
    | exact resolve eq28594 eq23517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28594
  have eq28607 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq28596 eq769
    | (have j0 := eq769 (M.op x y)
       grind)
    | (have r₁ := eq769 (M.op x y)
       have r₂ := eq28596
       grind)
    | exact resolve eq769 eq28596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28628 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq28607
  have eq30426 : y = (M.op y (M.op (M.op x (M.op (M.op x y) x)) (M.op x y))) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq19032
       have i₂ := eq21900
       grind)
    | exact superpose eq21900 eq19032
    | exact resolve eq19032 eq21900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19032 eq21900
  have eq30565 : y = (M.op y (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y))) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq23517 eq30426
    | exact resolve eq30426 eq23517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30426
  have eq30597 : y = (M.op y (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq30565
       have i₂ := eq17278 sF0
       grind)
    | exact superpose eq17278 eq30565
    | exact resolve eq30565 eq17278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30565
  have eq30617 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq28628 eq30597
    | exact resolve eq30597 eq28628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28628 eq30597
  have eq30667 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq697 y
       have i₂ := eq30617
       grind)
    | exact superpose eq30617 eq697
    | exact resolve eq697 eq30617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30617
  have eq41491 : (σ y) = (M.op y (M.op (M.op x y) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27531 eq23510
    | exact resolve eq23510 eq27531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27531
  have eq41517 : (σ y) = (M.op y (M.op (M.op x y) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq41491
  have eq41552 : (σ x) = (M.op y (M.op (M.op x y) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28409 eq41517
    | exact resolve eq41517 eq28409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41517
  have eq46422 : (M.op (σ y) (σ x)) = (M.op y (M.op (M.op x y) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27578 eq23510
    | exact resolve eq23510 eq27578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23510 eq27578
  have eq46435 : (M.op (σ y) (σ x)) = (M.op y (M.op (M.op x y) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq46422
  have eq46450 : (M.op (σ x) (σ x)) = (M.op y (M.op (M.op x y) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28409 eq46435
    | exact resolve eq46435 eq28409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28409 eq46435
  have eq46530 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41552 eq46450
    | exact resolve eq46450 eq41552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41552 eq46450
  have eq46622 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46530 eq246
    | exact resolve eq246 eq46530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq46801 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq46622
    | exact resolve eq46622 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46622
  have eq46900 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq769 x
       have i₂ := eq46801
       grind)
    | exact superpose eq46801 eq769
    | (have j0 := eq769 x
       grind)
    | (have r₁ := eq769 x
       have r₂ := eq46801
       grind)
    | exact resolve eq769 eq46801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46801
  have eq46926 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq46900
  have eq47075 : x = (M.op (M.op x y) (M.op x x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21504 x
       have i₂ := eq46926
       grind)
    | exact superpose eq46926 eq21504
    | exact resolve eq21504 eq46926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21504 eq46926
  have eq47096 : x = (M.op (M.op x y) (M.op x x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq47075
  have eq47128 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20396 eq47096
    | exact resolve eq47096 eq20396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20396 eq47096
  have eq47129 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq47128
  have eq47207 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47129 eq27
    | exact resolve eq27 eq47129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55020 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq19961
       grind)
    | exact superpose eq19961 eq40
    | exact resolve eq40 eq19961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19961
  have eq55064 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq55020
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq55020
    | exact resolve eq55020 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55020
  have eq55076 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq55064
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq55064
    | exact resolve eq55064 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55064
  have eq55087 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26523 eq55076
    | exact resolve eq55076 eq26523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26523 eq55076
  have eq55098 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq23517 eq55087
    | exact resolve eq55087 eq23517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55087
  have eq55099 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq55098
  have eq55114 : (τ (σ y)) = (k x x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq55099 eq98
    | exact resolve eq98 eq55099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55099
  have eq55162 : y = (k x x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq32 eq55114
    | exact resolve eq55114 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55114
  have eq55172 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq23517 eq55162
    | exact resolve eq55162 eq23517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23517 eq55162
  have eq55178 : y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq28596 eq55172
    | exact resolve eq55172 eq28596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28596 eq55172
  have eq55179 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq55178
  have eq55213 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq697 y
       have i₂ := eq55179
       grind)
    | exact superpose eq55179 eq697
    | exact resolve eq697 eq55179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55270 : y = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17264 y
       have i₂ := eq55179
       grind)
    | exact superpose eq55179 eq17264
    | exact resolve eq17264 eq55179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55273 : ∀ X0 : G, y = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17297 X0 y
       have i₂ := eq55179
       grind)
    | exact superpose eq55179 eq17297
    | exact resolve eq17297 eq55179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55285 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17927 y
       have i₂ := eq55179
       grind)
    | exact superpose eq55179 eq17927
    | exact resolve eq17927 eq55179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17927
  have eq55312 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq55179
       grind)
    | exact superpose eq55179 eq11
    | exact resolve eq11 eq55179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55179
  have eq55313 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq55312
  have eq55337 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq55273 x
       have i₂ := eq17747 sF0 x
       grind)
    | exact superpose eq17747 eq55273
    | exact resolve eq55273 eq17747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55273
  have eq57012 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq55313
       grind)
    | exact superpose eq55313 eq41
    | exact resolve eq41 eq55313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq57032 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 X0) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7791 y X0
       have i₂ := eq55313
       grind)
    | exact superpose eq55313 eq7791
    | (have j0 := eq7791 y x
       grind)
    | exact resolve eq7791 eq55313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7791
  have eq57043 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq57032 x
       have i₂ := eq17298 (σ sF0) x
       grind)
    | exact superpose eq17298 eq57032
    | exact resolve eq57032 eq17298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57032
  have eq57053 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq57012
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq57012
    | exact resolve eq57012 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57012
  have eq57057 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq57043
    | exact resolve eq57043 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57043
  have eq57062 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq57053
    | exact resolve eq57053 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57053
  have eq57064 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq57057
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq57057
    | exact resolve eq57057 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57057
  have eq57069 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq57064
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq57064
    | exact resolve eq57064 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57064
  have eq57854 : y = (k (M.op y (M.op x y)) (M.op y (M.op x y))) ∨ y = (M.op x y) ∨ (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) ∨ (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq55270
       have i₂ := eq11 (M.op y sF0) (M.op y sF0)
       grind)
    | exact superpose eq11 eq55270
    | (have j1 := eq11 (M.op y (M.op x y)) (M.op y (M.op x y))
       grind)
    | exact resolve eq55270 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57968 : y = (k (M.op y (M.op x y)) (M.op y (M.op x y))) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55270 eq11
    | exact resolve eq11 eq55270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55270
  have eq57969 : y = (k (M.op y (M.op x y)) (M.op y (M.op x y))) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq57968
  have eq57976 : y = (k (M.op y (M.op x y)) (M.op y (M.op x y))) ∨ y = (M.op x y) ∨ (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) := by grind
  clear eq57854
  have eq57984 : y = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30667 eq57969
    | exact resolve eq57969 eq30667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30667 eq57969
  have eq58075 : y = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) := by
    first
    | exact superpose eq55213 eq57976
    | exact resolve eq57976 eq55213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57976
  have eq58083 : y = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55213 eq57984
    | exact resolve eq57984 eq55213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57984
  have eq58142 : y = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq55213 eq58075
    | exact resolve eq58075 eq55213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55213 eq58075
  have eq58167 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ y = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq58142
       have i₂ := eq697 sF0
       grind)
    | exact superpose eq697 eq58142
    | exact resolve eq58142 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58142
  have eq58182 : y = (M.op (M.op x y) y) ∨ y = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq58083 eq58167
    | exact resolve eq58167 eq58083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58083 eq58167
  have eq58191 : y = (M.op x y) ∨ y = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55285 eq58182
    | exact resolve eq58182 eq55285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55285 eq58182
  have eq58192 : y = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq58191
  have eq59071 : y = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21496 eq58192
    | exact resolve eq58192 eq21496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21496 eq58192
  have eq59119 : y = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq59071
  have eq62325 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq59119
       grind)
    | exact superpose eq59119 eq40
    | exact resolve eq40 eq59119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq62333 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq824 x
       have i₂ := eq59119
       grind)
    | exact superpose eq59119 eq824
    | (have j0 := eq824 x
       grind)
    | exact resolve eq824 eq59119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824 eq59119
  have eq62366 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62333
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq62333
    | exact resolve eq62333 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62333
  have eq62368 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62325
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq62325
    | exact resolve eq62325 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62325
  have eq62376 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62366
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq62366
    | exact resolve eq62366 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62366
  have eq62377 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62368
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq62368
    | exact resolve eq62368 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62368
  have eq62383 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62376
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq62376
    | exact resolve eq62376 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62376
  have eq62403 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq62377 eq948
    | (have j0 := eq948 (σ x)
       grind)
    | exact resolve eq948 eq62377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62428 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq62403
    | exact resolve eq62403 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62403
  have eq62439 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46530 eq62428
    | exact resolve eq62428 eq46530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46530 eq62428
  have eq62443 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq62439
    | exact resolve eq62439 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62439
  have eq62444 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47129 eq62443
    | exact resolve eq62443 eq47129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47129 eq62443
  have eq62445 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq62444
       have r₂ := eq62383
       grind)
    | exact resolve eq62444 eq62383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62383 eq62444
  have eq62495 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq62445 eq176
    | exact resolve eq176 eq62445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq62445
  have eq62694 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq62495 eq62377
    | exact resolve eq62377 eq62495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62495
  have eq62724 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq62694
  have eq62949 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq62724 eq57062
    | exact resolve eq57062 eq62724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57062 eq62724
  have eq62950 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq62949
  have eq63024 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq62377 eq62950
    | exact resolve eq62950 eq62377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62377 eq62950
  have eq63112 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq63024
       have r₂ := eq47207
       grind)
    | exact resolve eq63024 eq47207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47207 eq63024
  have eq74528 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq57069 eq932
    | exact resolve eq932 eq57069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932 eq57069
  have eq74615 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq74528 eq267
    | exact resolve eq267 eq74528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq74528
  have eq74822 : y = (k y y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq74615
    | exact resolve eq74615 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74615
  have eq74847 : y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55313 eq74822
    | exact resolve eq74822 eq55313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55313 eq74822
  have eq74848 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq74847
  have eq74870 : (σ y) = (M.op (σ y) (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq74848 eq17908
    | exact resolve eq17908 eq74848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74874 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq74870
       have i₂ := eq17278 sF1
       grind)
    | exact superpose eq17278 eq74870
    | exact resolve eq74870 eq17278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74870
  have eq74898 : (σ (M.op x y)) = (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq74874 eq17297
    | exact resolve eq17297 eq74874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74874
  have eq74910 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq74898
       have i₂ := eq17278 sF3
       grind)
    | exact superpose eq17278 eq74898
    | exact resolve eq74898 eq17278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74898
  have eq75042 : ∀ X0 : G, (k X0 (M.op (σ y) (M.op (σ (M.op x y)) X0))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq74910 eq17865
    | exact resolve eq17865 eq74910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17865 eq74910
  have eq77164 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (σ y) (M.op (σ (M.op x y)) (τ X0))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq75042 eq35
    | exact resolve eq35 eq75042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq77259 : ∀ X0 : G, (k X0 (σ (M.op (σ y) (M.op (σ (M.op x y)) (τ X0))))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq77164 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq77164
    | exact resolve eq77164 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77164
  have eq82534 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (k x X0) (M.op (σ y) (M.op (σ (M.op x y)) (τ (k (σ x) (σ X0))))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq77259 eq44
    | exact resolve eq44 eq77259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq77259
  have eq82677 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (k x X0) (M.op (σ y) (M.op (σ (M.op x y)) (k x X0))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq45 eq82534
    | exact resolve eq82534 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq82534
  have eq82832 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (k (M.op x y) X0) (M.op (σ y) (M.op (σ (M.op x y)) (k (M.op x y) X0))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq63112 eq82677
    | exact resolve eq82677 eq63112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63112 eq82677
  have eq82935 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) ∨ y = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f82935_13 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (k (M.op x y) X0) (M.op (σ y) (M.op (σ (M.op x y)) (k (M.op x y) X0))))) ∨ y = (M.op x y) := by
      intro X0
      grind
    have f82935_14 : ∀ X0 : G, (k X0 (M.op (σ y) (M.op (σ (M.op x y)) X0))) = X0 ∨ y = (M.op x y) := by
      intro X0
      grind
    have f82935_16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
      intro X0 X1
      grind
    have f82935_23 : (k (σ x) (σ X0)) ≠ (σ (k (M.op x y) X0)) := by grind
    have f82935_24 : y ≠ (M.op x y) := by grind
    have f82935_27 : ∀ X0 : G, (k X0 (M.op (σ y) (M.op (σ (M.op x y)) X0))) = X0 := by
      intro X0
      first
      | (have j0 := f82935_14 X0
         grind)
      | (have r₁ := f82935_14 X0
         have r₂ := f82935_24
         grind)
      | exact resolve f82935_14 f82935_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f82935_28 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (k (M.op x y) X0) (M.op (σ y) (M.op (σ (M.op x y)) (k (M.op x y) X0))))) := by
      intro X0
      first
      | (have j0 := f82935_13 X0
         grind)
      | (have r₁ := f82935_13 X0
         have r₂ := f82935_24
         grind)
      | exact resolve f82935_13 f82935_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f82935_29 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) := by
      intro X0
      first
      | (have i₁ := f82935_28 X0
         have i₂ := f82935_27 (k (M.op x y) X0)
         grind)
      | exact superpose f82935_27 f82935_28
      | exact resolve f82935_28 f82935_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f82935_30 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (k x X0)) := by
      intro X0
      first
      | (have i₁ := f82935_29 X0
         have i₂ := f82935_16 x X0
         grind)
      | exact superpose f82935_16 f82935_29
      | exact resolve f82935_29 f82935_16
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f82935_64 : (k (σ x) (σ X0)) ≠ (σ (k x X0)) := by
      first
      | (have i₁ := f82935_23
         have i₂ := f82935_30 X0
         grind)
      | exact superpose f82935_30 f82935_23
      | exact resolve f82935_23 f82935_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f82935_65 : False := by
      first
      | (have r₁ := f82935_64
         have r₂ := f82935_16 x X0
         grind)
      | exact resolve f82935_64 f82935_16
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f82935_65
  clear eq75042 eq82832
  have eq83012 : ∀ X0 : G, (k (σ x) (σ X0)) = (k (σ (M.op x y)) (σ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq38 eq82935
    | exact resolve eq82935 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq82935
  have eq83717 : (σ (M.op x y)) = (k (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq83012 eq17389
    | exact resolve eq17389 eq83012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17389 eq83012
  have eq83746 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55337 eq83717
    | exact resolve eq83717 eq55337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55337 eq83717
  have eq83780 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq83746
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq83746
    | exact resolve eq83746 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83746
  have eq83790 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19514 eq83780
    | exact resolve eq83780 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19514 eq83780
  have eq83924 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq83790 eq74848
    | exact resolve eq74848 eq83790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74848
  have eq84021 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq83924
  have eq84068 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq84021
    | exact resolve eq84021 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq84021
  have eq84146 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq84068 eq27
    | exact resolve eq27 eq84068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84068
  have eq84185 : y = (M.op x y) := by
    first
    | (have r₁ := eq84146
       have r₂ := eq83790
       grind)
    | exact resolve eq84146 eq83790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83790 eq84146
  have eq84186 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq84185
       grind)
    | exact superpose eq84185 eq18
    | exact resolve eq18 eq84185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84187 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq84185
       grind)
    | exact superpose eq84185 eq24
    | exact resolve eq24 eq84185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq84191 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq190
       have i₂ := eq84185
       grind)
    | exact superpose eq84185 eq190
    | exact resolve eq190 eq84185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq84264 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24826
       have i₂ := eq84185
       grind)
    | exact superpose eq84185 eq24826
    | exact resolve eq24826 eq84185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24826
  have eq84318 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq84187 eq20
    | exact resolve eq20 eq84187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84187
  have eq90860 : y = (k y (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq953 x
       have i₂ := eq26678
       grind)
    | exact superpose eq26678 eq953
    | (have j0 := eq953 x
       grind)
    | exact resolve eq953 eq26678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953 eq26678
  have eq90949 : y = (k y (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90860
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90860
    | exact resolve eq90860 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq90860
  have eq90961 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90949
       have i₂ := eq84185
       grind)
    | exact superpose eq84185 eq90949
    | exact resolve eq90949 eq84185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90949
  have eq90970 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq84264 eq90961
    | exact resolve eq90961 eq84264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90961
  have eq109510 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20136 eq98
    | exact resolve eq98 eq20136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq20136
  have eq109570 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq32 eq109510
    | exact resolve eq109510 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq109510
  have eq109575 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq109570
       have i₂ := eq84185
       grind)
    | exact superpose eq84185 eq109570
    | exact resolve eq109570 eq84185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109570
  have eq111142 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq109575 eq24663
    | exact resolve eq24663 eq109575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24663
  have eq111303 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq109575 eq11
    | exact resolve eq11 eq109575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109575
  have eq111304 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by grind
  clear eq111303
  have eq111317 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq111142
  have eq111400 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq769 x
       have i₂ := eq111317
       grind)
    | exact superpose eq111317 eq769
    | (have j0 := eq769 x
       grind)
    | exact resolve eq769 eq111317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111317
  have eq113197 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq111304 eq116
    | exact resolve eq116 eq111304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111304
  have eq113281 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq113197
       have i₂ := eq84185
       grind)
    | exact superpose eq84185 eq113197
    | exact resolve eq113197 eq84185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113197
  have eq113289 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq113281
    | exact resolve eq113281 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113281
  have eq120287 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq769 x
       have i₂ := eq113289
       grind)
    | exact superpose eq113289 eq769
    | (have j0 := eq769 x
       grind)
    | exact resolve eq769 eq113289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120296 : x = (M.op x (M.op x (M.op x y))) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq948 x
       have i₂ := eq113289
       grind)
    | exact superpose eq113289 eq948
    | (have j0 := eq948 x
       grind)
    | exact resolve eq948 eq113289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948 eq113289
  have eq120340 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq84186 eq120296
    | exact resolve eq120296 eq84186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120296
  have eq120354 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq84186 eq120340
    | exact resolve eq120340 eq84186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120340
  have eq120364 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq120354
       have r₂ := eq120287
       grind)
    | exact resolve eq120354 eq120287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120287 eq120354
  have eq122199 : x = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq120364 eq84264
    | exact resolve eq84264 eq120364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84264 eq120364
  have eq122236 : x = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq122199
  have eq122262 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq90970 eq122236
    | exact resolve eq122236 eq90970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90970 eq122236
  have eq122282 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq122262
       have r₂ := eq111400
       grind)
    | exact resolve eq122262 eq111400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111400 eq122262
  have eq122318 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq189
       have i₂ := eq122282
       grind)
    | exact superpose eq122282 eq189
    | exact resolve eq189 eq122282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq122282
  have eq122528 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq122318
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq122318
    | exact resolve eq122318 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq122318
  have eq122549 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq24585 (σ x)
       grind)
    | (have r₁ := eq122528
       have r₂ := eq24585 (σ x)
       grind)
    | (have r₁ := eq122528
       have r₂ := eq24585 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq122528 eq24585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24585 eq122528
  have eq122602 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq122549 eq24632
    | exact resolve eq24632 eq122549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24632
  have eq122612 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq122549 eq769
    | (have j0 := eq769 (σ x)
       grind)
    | (have r₁ := eq769 (σ x)
       have r₂ := eq122549
       grind)
    | exact resolve eq769 eq122549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122549
  have eq122641 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq122612
  have eq122643 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq122602
  have eq122672 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq122643 eq27
    | exact resolve eq27 eq122643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122643
  have eq122681 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq122672
       have r₂ := eq84318
       grind)
    | exact resolve eq122672 eq84318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122672
  have eq123665 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq122641 eq22348
    | exact resolve eq22348 eq122641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22348 eq122641
  have eq123877 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq123665
  have eq124010 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24565 eq123877
    | exact resolve eq123877 eq24565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24565 eq123877
  have eq124011 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq124010
  have eq124042 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq122681 eq124011
    | exact resolve eq124011 eq122681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122681 eq124011
  have eq124043 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq124042
  have eq124071 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq124043 eq27
    | exact resolve eq27 eq124043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq124072 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ x))) := by
    first
    | exact superpose eq124043 eq19033
    | exact resolve eq19033 eq124043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19033 eq124043
  have eq124115 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq124072
       have i₂ := eq17278 sF2
       grind)
    | exact superpose eq17278 eq124072
    | exact resolve eq124072 eq17278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124072
  have eq124116 : (σ x) ≠ (σ y) := by
    first
    | exact superpose eq84318 eq124071
    | exact resolve eq124071 eq84318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124071
  have eq124167 : (σ x) = (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) := by
    first
    | exact superpose eq124115 eq17297
    | exact resolve eq17297 eq124115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124171 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y))) := by
    first
    | exact superpose eq124115 eq17908
    | exact resolve eq17908 eq124115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17908 eq124115
  have eq124175 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq124171
       have i₂ := eq17278 sF3
       grind)
    | exact superpose eq17278 eq124171
    | exact resolve eq124171 eq17278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124171
  have eq124177 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq124167
       have i₂ := eq17278 sF3
       grind)
    | exact superpose eq17278 eq124167
    | exact resolve eq124167 eq17278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124167
  have eq124238 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq124177 eq697
    | exact resolve eq697 eq124177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq124307 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) := by
    first
    | exact superpose eq124177 eq17264
    | exact resolve eq17264 eq124177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17264
  have eq124309 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
    first
    | exact superpose eq124177 eq17278
    | exact resolve eq17278 eq124177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17278
  have eq124310 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq124177 eq17297
    | exact resolve eq17297 eq124177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17297
  have eq124312 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq124177 eq17298
    | exact resolve eq17298 eq124177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124316 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq124177 eq17856
    | exact resolve eq17856 eq124177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17856
  have eq124382 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq124310 x
       have i₂ := eq17747 sF2 x
       grind)
    | exact superpose eq17747 eq124310
    | exact resolve eq124310 eq17747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17747 eq124310
  have eq125476 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq124238 eq124309
    | exact resolve eq124309 eq124238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124309
  have eq126010 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq124307 eq17298
    | exact resolve eq17298 eq124307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17298 eq124307
  have eq126094 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq124238 eq126010
    | exact resolve eq126010 eq124238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124238 eq126010
  have eq128467 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq124175
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq124175
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq124175 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124175
  have eq128489 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq128467
  have eq128501 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (k (σ y) (σ y))) := by
    first
    | exact superpose eq124177 eq128489
    | exact resolve eq128489 eq124177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128489
  have eq128512 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (k (σ y) (σ y))) := by
    first
    | (have r₁ := eq128501
       have r₂ := eq124116
       grind)
    | exact resolve eq128501 eq124116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128501
  have eq131550 : (k (σ y) (σ y)) = (M.op (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) (M.op (σ x) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq128512 eq17862
    | exact resolve eq17862 eq128512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17862
  have eq131551 : (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ x))) (k (σ y) (σ y))) := by
    first
    | exact superpose eq128512 eq17863
    | exact resolve eq17863 eq128512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17863
  have eq131566 : (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) = (M.op (σ y) (k (σ y) (σ y))) := by
    first
    | exact superpose eq124382 eq131551
    | exact resolve eq131551 eq124382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131551
  have eq131567 : (k (σ y) (σ y)) = (M.op (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) (σ y)) := by
    first
    | exact superpose eq124382 eq131550
    | exact resolve eq131550 eq124382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124382 eq131550
  have eq131574 : (k (σ y) (σ y)) = (M.op (M.op (σ y) (k (σ y) (σ y))) (σ y)) := by
    first
    | exact superpose eq131566 eq131567
    | exact resolve eq131567 eq131566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131566 eq131567
  have eq141108 : (M.op (σ y) (k (σ y) (σ y))) = (M.op (M.op (σ x) (σ x)) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq126094 sF3
       have i₂ := eq17343 sF3
       grind)
    | exact superpose eq17343 eq126094
    | (have j1 := eq17343 (σ y)
       grind)
    | exact resolve eq126094 eq17343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17343 eq126094
  have eq141310 : (M.op (σ x) (σ x)) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq128512 eq141108
    | exact resolve eq141108 eq128512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128512 eq141108
  have eq141405 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (k (σ y) (σ y))) := by
    first
    | exact superpose eq124177 eq141310
    | exact resolve eq141310 eq124177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124177 eq141310
  have eq141477 : (M.op (σ x) (σ x)) = (M.op (σ y) (k (σ y) (σ y))) := by
    first
    | (have r₁ := eq141405
       have r₂ := eq124116
       grind)
    | exact resolve eq141405 eq124116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141405
  have eq141631 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq141477 eq131574
    | exact resolve eq131574 eq141477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131574 eq141477
  have eq141671 : (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq125476 eq141631
    | exact resolve eq141631 eq125476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125476 eq141631
  have eq141714 : (τ (σ x)) = (k y y) := by
    first
    | exact superpose eq141671 eq116
    | exact resolve eq116 eq141671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq141801 : (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq141714
       have i₂ := eq84185
       grind)
    | exact superpose eq84185 eq141714
    | exact resolve eq141714 eq84185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84185 eq141714
  have eq141810 : x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq141801
    | exact resolve eq141801 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq141801
  have eq141866 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq141810 eq769
    | (have j0 := eq769 (M.op x y)
       grind)
    | exact resolve eq769 eq141810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq141885 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq141810 eq7790
    | (have j0 := eq7790 X0 (M.op x y)
       grind)
    | exact resolve eq7790 eq141810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7790 eq141810
  have eq141899 : (M.op x y) = (M.op x (M.op x x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq141885 x
       have i₂ := eq17310 x x
       grind)
    | exact superpose eq17310 eq141885
    | exact resolve eq141885 eq17310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17310 eq141885
  have eq141915 : (M.op x y) = (M.op (σ y) (M.op (σ x) x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq141899
       have i₂ := eq124312 x
       grind)
    | exact superpose eq124312 eq141899
    | exact resolve eq141899 eq124312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124312 eq141899
  have eq142746 : x = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq141915 eq124316
    | exact resolve eq124316 eq141915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124316 eq141915
  have eq142779 : x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq84186 eq142746
    | exact resolve eq142746 eq84186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84186 eq142746
  have eq142791 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq142779
       have r₂ := eq141866
       grind)
    | exact resolve eq142779 eq141866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141866 eq142779
  have eq142874 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq142791 eq84191
    | exact resolve eq84191 eq142791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84191 eq142791
  have eq143095 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq142874
    | exact resolve eq142874 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq142874
  have eq143121 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq84318 eq143095
    | exact resolve eq143095 eq84318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84318 eq143095
  have eq143136 : (σ x) = (σ y) := by
    first
    | exact superpose eq141671 eq143121
    | exact resolve eq143121 eq141671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141671 eq143121
  have eq143142 : False := by grind
  exact eq143142

/-- `Equation934`: `x = y ◇ ((y ◇ z) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_y_pxx_pxy_pyx_Equation934 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law934 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law934.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X2) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 (M.op (M.op X1 X2) (M.op X2 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X3 X0)) = (M.op X1 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X3) (M.op X3 X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq15
    | exact resolve eq15 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq65 (τ X0)
       grind)
    | exact superpose eq65 eq32
    | exact resolve eq32 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq77 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq70
    | exact resolve eq70 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq68
    | exact resolve eq68 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq68
  have eq94 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq9
    | exact resolve eq9 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq9
    | exact resolve eq9 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1 (τ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq9
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq94 X0 (σ X0)
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq94
    | exact resolve eq94 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq79 (M.op X0 X0)
       grind)
    | exact superpose eq79 eq113
    | exact resolve eq113 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq132 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (M.op (σ X1) X0)) = (M.op (σ X1) (M.op (σ (M.op X1 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X1 (M.op (σ (M.op X1 X1)) (M.op (σ X1) X0))
       have i₂ := eq95 X1 X0
       grind)
    | exact superpose eq95 eq95
    | exact resolve eq95 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq132 X1 X0
       grind)
    | exact superpose eq132 eq95
    | exact resolve eq95 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq132
  have eq154 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (M.op (σ (τ X0)) (M.op (σ (τ (M.op X0 X0))) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141 (τ X0) X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq141
    | exact resolve eq141 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq164 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (M.op (σ (τ X0)) (M.op (M.op X0 X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq154 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq154
    | exact resolve eq154 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq168 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq164 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq164
    | exact resolve eq164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq171 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ X0) (M.op (τ (M.op X0 X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq168 (τ X0) X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq168
    | exact resolve eq168 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X2 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq168 X1 (M.op (M.op (M.op X1 X1) X2) (M.op X2 X0))
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq168
    | exact resolve eq168 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X2) X0)) = (M.op X2 (M.op (M.op X2 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X2 X2) X0)) X1 X2
       have i₂ := eq168 X2 X0
       grind)
    | exact superpose eq168 eq9
    | exact resolve eq9 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq191 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq289 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq104 X0 (τ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq104
    | exact resolve eq104 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq289 X0
       have i₂ := eq77 (M.op X0 X0)
       grind)
    | exact superpose eq77 eq289
    | exact resolve eq289 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq387 : ∀ X0 : G, (τ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq171 X0 (τ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))))
       have i₂ := eq303 (M.op X0 X0)
       grind)
    | exact superpose eq303 eq171
    | exact resolve eq171 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq394 : ∀ X0 : G, (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0)))) = (τ (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq387 X0
       have i₂ := eq172 (M.op X0 X0) X0 (M.op X0 X0)
       grind)
    | exact superpose eq172 eq387
    | exact resolve eq387 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq387
  have eq435 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X3) (M.op X3 X2)) X4) (M.op X4 X0)) = (M.op X1 (M.op X2 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 X2 X1 X3 (M.op (M.op (M.op (M.op X1 X3) (M.op X3 X2)) X4) (M.op X4 X0))
       have i₂ := eq9 X0 (M.op (M.op X1 X3) (M.op X3 X2)) X4
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X2 X0)) = (M.op X4 (M.op (M.op (M.op (M.op (M.op X1 X3) (M.op X3 X2)) X5) (M.op X5 X4)) X0)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq62 X2 X1 X3 (M.op X4 (M.op (M.op (M.op (M.op (M.op X1 X3) (M.op X3 X2)) X5) (M.op X5 X4)) X0))
       have i₂ := eq62 X4 (M.op (M.op X1 X3) (M.op X3 X2)) X5 X0
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op X1 X2) X1 X2 (M.op (M.op X2 (M.op X1 X2)) X0)
       have i₂ := eq9 X0 (M.op X1 X2) (M.op X2 (M.op X1 X2))
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq460 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op X4 (M.op (M.op X1 (M.op X2 X4)) X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq439 X0 X1 X2 x X4 x
       have i₂ := eq435 X4 X1 X2 x x
       grind)
    | exact superpose eq435 eq439
    | exact resolve eq439 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq505 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op X1 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq443 X2 (M.op (M.op X1 X0) X1) (M.op X1 X0)
       have i₂ := eq9 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq9 eq443
    | exact resolve eq443 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq516 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X1) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X0 X1)
       have i₂ := eq443 (M.op (M.op X0 X1) X2) X0 X1
       grind)
    | exact superpose eq443 eq9
    | exact resolve eq9 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq565 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq505 (M.op (M.op X1 X2) (M.op X2 X0)) X1 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq505
    | exact resolve eq505 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op X0 X1) X0) X2) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq505 X0 X0 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq505 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq505
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq505 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X0) X1
       have i₂ := eq505 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq505 eq9
    | exact resolve eq9 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op (σ X1) X0) (M.op X0 (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X1 (M.op (σ X1) X0)
       have i₂ := eq505 X0 (σ X1) (σ (M.op X1 X1))
       grind)
    | exact superpose eq505 eq94
    | exact resolve eq94 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 : G, (τ X1) = (M.op (M.op (τ X1) X0) (M.op X0 (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X1 (M.op (τ X1) X0)
       have i₂ := eq505 X0 (τ X1) (τ (M.op X1 X1))
       grind)
    | exact superpose eq505 eq104
    | exact resolve eq104 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq633 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 X2) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq570 X0 X1 X2
       have i₂ := eq505 X1 X0 X2
       grind)
    | exact superpose eq505 eq570
    | (have j0 := eq570 X0 X1 X2
       grind)
    | exact resolve eq570 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq645 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X2 X1) X4) (M.op X4 X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq435 X0 X1 X2 x X4
       have i₂ := eq565 X2 X1 x X4
       grind)
    | exact superpose eq565 eq435
    | exact resolve eq435 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq1665 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X0) = (M.op X4 (M.op (M.op X4 X1) (M.op (M.op X2 X3) (M.op X3 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 (M.op (M.op X2 X3) (M.op X3 X0)) X4 X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1675 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X3)) X0) = (M.op X4 (M.op (M.op X4 X1) (M.op X3 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 (M.op X3 (M.op X2 X0)) X4 X1 (M.op X2 X3)
       have i₂ := eq586 X3 X2 X0
       grind)
    | exact superpose eq586 eq63
    | exact resolve eq63 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1709 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X2) X0)) X3) (M.op X3 X4)) = (M.op X2 (M.op X0 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 X4 X2 (M.op X1 (M.op (M.op X1 X2) X0)) X3
       have i₂ := eq516 X1 X2 X0
       grind)
    | exact superpose eq516 eq63
    | exact resolve eq63 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1717 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (σ (M.op X0 X0))) X2) (M.op X2 X3)) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X3 (M.op (σ X0) X1) (M.op X1 (σ (M.op X0 X0))) X2
       have i₂ := eq587 X1 X0
       grind)
    | exact superpose eq587 eq63
    | exact resolve eq63 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq1718 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (τ (M.op X0 X0))) X2) (M.op X2 X3)) = (M.op (M.op (τ X0) X1) (M.op (τ X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X3 (M.op (τ X0) X1) (M.op X1 (τ (M.op X0 X0))) X2
       have i₂ := eq588 X1 X0
       grind)
    | exact superpose eq588 eq63
    | exact resolve eq63 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq1763 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ (M.op X0 (M.op (M.op X0 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X1
       have i₂ := eq63 X1 X0 X1 X1
       grind)
    | exact superpose eq63 eq303
    | exact resolve eq303 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq1764 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 (M.op (M.op X0 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq120 X1
       have i₂ := eq63 X1 X0 X1 X1
       grind)
    | exact superpose eq63 eq120
    | exact resolve eq120 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq1815 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X0) X2) X4) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq505 (M.op (M.op X3 X0) X2) X3 X4
       have i₂ := eq63 X2 X3 X0 X1
       grind)
    | exact superpose eq63 eq505
    | exact resolve eq505 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1843 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X3 X0) X2) X4) = (M.op (M.op (M.op X2 X0) X3) X4) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1815 X0 x X2 X3 X4
       have i₂ := eq565 X2 X0 x X3
       grind)
    | exact superpose eq565 eq1815
    | exact resolve eq1815 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565 eq1815
  have eq1893 : ∀ X0 X1 X3 : G, (M.op (M.op (τ X0) X1) (M.op (τ X0) X3)) = (M.op (τ (M.op X0 X0)) (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1718 X0 X1 x X3
       have i₂ := eq645 X3 (τ (M.op X0 X0)) X1 x
       grind)
    | exact superpose eq645 eq1718
    | exact resolve eq1718 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq1894 : ∀ X0 X1 X3 : G, (M.op (M.op (σ X0) X1) (M.op (σ X0) X3)) = (M.op (σ (M.op X0 X0)) (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1717 X0 X1 x X3
       have i₂ := eq645 X3 (σ (M.op X0 X0)) X1 x
       grind)
    | exact superpose eq645 eq1717
    | exact resolve eq1717 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717
  have eq1899 : ∀ X0 X1 X2 X4 : G, (M.op X2 (M.op X0 X4)) = (M.op (M.op (M.op X1 X2) X0) (M.op X1 X4)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1709 X0 X1 X2 x X4
       have i₂ := eq645 X4 (M.op (M.op X1 X2) X0) X1 x
       grind)
    | exact superpose eq645 eq1709
    | exact resolve eq1709 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1709
  have eq1911 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1665 X0 X1 X2 X3 x
       have i₂ := eq1675 X0 X1 X3 (M.op X2 X3) x
       grind)
    | exact superpose eq1675 eq1665
    | exact resolve eq1665 eq1675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665 eq1675
  have eq2036 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X1) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1764 x X0
       have i₂ := eq63 X0 x X0 X1
       grind)
    | exact superpose eq63 eq1764
    | exact resolve eq1764 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq2485 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X1) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1763 x X0
       have i₂ := eq63 X0 x X0 X1
       grind)
    | exact superpose eq63 eq1763
    | exact resolve eq1763 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1763
  have eq3893 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X4 X3))) X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq516 X4 X3 (M.op (M.op X0 (M.op X1 (M.op X4 X3))) X2)
       have i₂ := eq460 X2 X0 X1 (M.op X4 X3)
       grind)
    | exact superpose eq460 eq516
    | exact resolve eq516 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3910 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op X3 (M.op X2 (M.op X1 (M.op X3 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1911 X0 X1 X2 X3
       have i₂ := eq3893 X1 X3 X0 X3 X2
       grind)
    | exact superpose eq3893 eq1911
    | exact resolve eq1911 eq3893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq4167 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op (M.op X3 X4) X0)))) = (M.op (M.op (M.op X2 X1) X4) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq645 (M.op X3 (M.op (M.op X3 X4) X0)) X1 X2 X4
       have i₂ := eq516 X3 X4 X0
       grind)
    | exact superpose eq516 eq645
    | exact resolve eq645 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq4640 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq233 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq4645 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4640 X0 X1
       have j1 := eq633 X1 X0 x
       grind)
    | (have r₁ := eq4640 X0 X1
       have r₂ := eq633 X0 X1 X0
       grind)
    | (have r₁ := eq4640 X1 X0
       have r₂ := eq633 X0 X1 X1
       grind)
    | (have r₁ := eq4640 X1 X1
       have r₂ := eq633 (M.op X1 X1) X1 x
       grind)
    | exact resolve eq4640 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq4640
  have eq4821 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X1
       have i₂ := eq4645 (σ X1) X0
       grind)
    | (have i₁ := eq79 X0
       have i₂ := eq4645 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq4645 eq79
    | (have j1 := eq4645 (σ X1) X0
       grind)
    | exact resolve eq79 eq4645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5870 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op X1 (M.op X2 (M.op X0 (M.op X3 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq460 (M.op X0 (M.op X3 X4)) X1 X2 X3
       have i₂ := eq3910 X4 X0 (M.op X1 (M.op X2 X3)) X3
       grind)
    | exact superpose eq3910 eq460
    | exact resolve eq460 eq3910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3910
  have eq5963 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X2 (M.op X0 (M.op X1 X4)))) = (M.op X1 (M.op X2 (M.op X0 (M.op X3 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5870 X0 X1 X2 X3 X4
       have i₂ := eq3893 X0 X1 X4 X3 X2
       grind)
    | exact superpose eq3893 eq5870
    | exact resolve eq5870 eq3893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893 eq5870
  have eq6387 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq4821 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq4821 (σ X0) X1
       grind)
    | exact superpose eq4821 eq10
    | (have j1 := eq4821 X0 X1
       grind)
    | exact resolve eq10 eq4821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4821
  have eq11082 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq6387 (σ X0) X1
       grind)
    | exact superpose eq6387 eq15
    | (have j1 := eq6387 (σ X0) X1
       grind)
    | exact resolve eq15 eq6387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6387
  have eq11094 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11082 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11082
    | (have j0 := eq11082 X0 X1
       grind)
    | exact resolve eq11082 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11082
  have eq18458 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11094 X0 X1
       have i₂ := eq4645 X1 X0
       grind)
    | exact superpose eq4645 eq11094
    | (have j0 := eq11094 X0 X1
       have j1 := eq4645 X1 X0
       grind)
    | exact resolve eq11094 eq4645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645 eq11094
  have eq18635 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq18458 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18458
  have eq23327 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18635 x y
       grind)
    | exact superpose eq18635 eq16
    | (have j1 := eq18635 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq18635 x y
       grind)
    | exact resolve eq16 eq18635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23568 : x = (M.op y y) := by grind
  clear eq23327
  have eq23701 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq94 y X0
       have i₂ := eq23568
       grind)
    | exact superpose eq23568 eq94
    | exact resolve eq94 eq23568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq23702 : ∀ X0 : G, (τ y) = (M.op X0 (M.op (M.op X0 (τ y)) (τ x))) := by
    intro X0
    first
    | (have i₁ := eq104 y X0
       have i₂ := eq23568
       grind)
    | exact superpose eq23568 eq104
    | exact resolve eq104 eq23568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq23726 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq18635 X0 y
       have i₂ := eq23568
       grind)
    | exact superpose eq23568 eq18635
    | (have j0 := eq18635 X0 y
       grind)
    | exact resolve eq18635 eq23568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18635
  have eq23728 : ∀ X0 : G, (M.op y (M.op x (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq23568
       grind)
    | exact superpose eq23568 eq9
    | exact resolve eq9 eq23568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23758 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) y) X1) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1843 y X0 y X1
       have i₂ := eq23568
       grind)
    | exact superpose eq23568 eq1843
    | exact resolve eq1843 eq23568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23769 : (σ y) = (M.op (σ y) (σ (M.op x x))) := by
    first
    | (have i₁ := eq2036 y y
       have i₂ := eq23568
       grind)
    | exact superpose eq23568 eq2036
    | exact resolve eq2036 eq23568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23771 : (τ y) = (M.op (τ y) (τ (M.op x x))) := by
    first
    | (have i₁ := eq2485 y y
       have i₂ := eq23568
       grind)
    | exact superpose eq23568 eq2485
    | exact resolve eq2485 eq23568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2485
  have eq23777 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq23728 y
       have i₂ := eq23568
       grind)
    | exact superpose eq23568 eq23728
    | exact resolve eq23728 eq23568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23778 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq23728 (M.op x (M.op y X0))
       have i₂ := eq23728 X0
       grind)
    | exact superpose eq23728 eq23728
    | exact resolve eq23728 eq23728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23791 : ∀ X0 X1 : G, (M.op (M.op y y) X1) = (M.op y (M.op x (M.op X0 (M.op (M.op X0 y) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23728 (M.op (M.op y y) X1)
       have i₂ := eq177 X1 X0 y
       grind)
    | (have i₁ := eq23728 (M.op (M.op y x) X0)
       have i₂ := eq177 X0 y x
       grind)
    | exact superpose eq177 eq23728
    | exact resolve eq23728 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq23728
  have eq23914 : ∀ X1 : G, (M.op (M.op y y) X1) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq23791 x X1
       have i₂ := eq4167 X1 y x x y
       grind)
    | exact superpose eq4167 eq23791
    | exact resolve eq23791 eq4167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4167 eq23791
  have eq23939 : y = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq23777
       have i₂ := eq23778 x
       grind)
    | exact superpose eq23778 eq23777
    | exact resolve eq23777 eq23778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23777 eq23778
  have eq23961 : ∀ X1 : G, (M.op (M.op y y) X1) = (M.op (M.op x x) X1) := by
    intro X1
    first
    | (have i₁ := eq23914 X1
       have i₂ := eq23758 x X1
       grind)
    | exact superpose eq23758 eq23914
    | exact resolve eq23914 eq23758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23758 eq23914
  have eq23977 : ∀ X1 : G, (M.op x X1) = (M.op (M.op x x) X1) := by
    intro X1
    first
    | (have i₁ := eq23961 X1
       have i₂ := eq23568
       grind)
    | exact superpose eq23568 eq23961
    | exact resolve eq23961 eq23568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23961
  have eq26063 : ∀ X0 : G, (M.op x (M.op x (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq586 x x X0
       have i₂ := eq23977 (M.op x (M.op x X0))
       grind)
    | exact superpose eq23977 eq586
    | exact resolve eq586 eq23977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq26812 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (σ (M.op x x)) (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq460 X1 X0 (σ y) (σ (M.op x x))
       have i₂ := eq23769
       grind)
    | exact superpose eq23769 eq460
    | exact resolve eq460 eq23769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26813 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (M.op (σ y) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq505 (σ (M.op x x)) (σ y) X0
       have i₂ := eq23769
       grind)
    | exact superpose eq23769 eq505
    | exact resolve eq505 eq23769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26840 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) (M.op X0 X1)) = (M.op (M.op (σ y) X0) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1899 X0 (σ y) (σ (M.op x x)) X1
       have i₂ := eq23769
       grind)
    | exact superpose eq23769 eq1899
    | exact resolve eq1899 eq23769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26854 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) (M.op X0 X1)) = (M.op (σ (M.op y y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26840 X0 X1
       have i₂ := eq1894 y X0 X1
       grind)
    | exact superpose eq1894 eq26840
    | exact resolve eq26840 eq1894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894 eq26840
  have eq26862 : ∀ X0 : G, (M.op (σ (M.op y y)) X0) = (M.op (σ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq26813 X0
       have i₂ := eq79 y
       grind)
    | exact superpose eq79 eq26813
    | exact resolve eq26813 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq26813
  have eq26877 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) (M.op X0 X1)) = (M.op (σ x) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26854 X0 X1
       have i₂ := eq23568
       grind)
    | exact superpose eq23568 eq26854
    | exact resolve eq26854 eq23568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26854
  have eq26885 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq26862 X0
       have i₂ := eq23568
       grind)
    | exact superpose eq23568 eq26862
    | exact resolve eq26862 eq23568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26862
  have eq26900 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (σ x) (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26812 X0 X1
       have i₂ := eq26877 (M.op X0 (σ y)) X1
       grind)
    | exact superpose eq26877 eq26812
    | exact resolve eq26812 eq26877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26812 eq26877
  have eq26965 : ∀ X0 X1 : G, (M.op X0 (M.op (τ y) X1)) = (M.op (τ (M.op x x)) (M.op (M.op X0 (τ y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq460 X1 X0 (τ y) (τ (M.op x x))
       have i₂ := eq23771
       grind)
    | exact superpose eq23771 eq460
    | exact resolve eq460 eq23771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq26966 : ∀ X0 : G, (M.op (τ (M.op x x)) X0) = (M.op (M.op (τ y) (τ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq505 (τ (M.op x x)) (τ y) X0
       have i₂ := eq23771
       grind)
    | exact superpose eq23771 eq505
    | exact resolve eq505 eq23771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq26971 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (τ (M.op x x)))) = (M.op (M.op (M.op X1 X0) (τ y)) (τ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq645 (τ (M.op x x)) X0 X1 (τ y)
       have i₂ := eq23771
       grind)
    | exact superpose eq23771 eq645
    | exact resolve eq645 eq23771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq26993 : ∀ X0 X1 : G, (M.op (τ (M.op x x)) (M.op X0 X1)) = (M.op (M.op (τ y) X0) (M.op (τ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1899 X0 (τ y) (τ (M.op x x)) X1
       have i₂ := eq23771
       grind)
    | exact superpose eq23771 eq1899
    | exact resolve eq1899 eq23771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899
  have eq27007 : ∀ X0 X1 : G, (M.op (τ (M.op x x)) (M.op X0 X1)) = (M.op (τ (M.op y y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26993 X0 X1
       have i₂ := eq1893 y X0 X1
       grind)
    | exact superpose eq1893 eq26993
    | exact resolve eq26993 eq1893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1893 eq26993
  have eq27013 : ∀ X0 : G, (M.op (τ (M.op y y)) X0) = (M.op (τ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq26966 X0
       have i₂ := eq77 y
       grind)
    | exact superpose eq77 eq26966
    | exact resolve eq26966 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq26966
  have eq27027 : ∀ X0 X1 : G, (M.op (τ (M.op x x)) (M.op X0 X1)) = (M.op (τ x) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27007 X0 X1
       have i₂ := eq23568
       grind)
    | exact superpose eq23568 eq27007
    | exact resolve eq27007 eq23568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27007
  have eq27032 : ∀ X0 : G, (M.op (τ x) X0) = (M.op (τ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq27013 X0
       have i₂ := eq23568
       grind)
    | exact superpose eq23568 eq27013
    | exact resolve eq27013 eq23568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23568 eq27013
  have eq27055 : ∀ X0 X1 : G, (M.op X0 (M.op (τ y) X1)) = (M.op (τ x) (M.op (M.op X0 (τ y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26965 X0 X1
       have i₂ := eq27027 (M.op X0 (τ y)) X1
       grind)
    | exact superpose eq27027 eq26965
    | exact resolve eq26965 eq27027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26965 eq27027
  have eq30320 : (σ y) = (M.op (σ x) (M.op (M.op (σ (M.op x x)) (σ y)) (σ x))) := by
    first
    | (have i₁ := eq26885 (M.op (M.op (σ (M.op x x)) (σ y)) (σ x))
       have i₂ := eq23701 (σ (M.op x x))
       grind)
    | exact superpose eq23701 eq26885
    | exact resolve eq26885 eq23701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23701
  have eq30344 : (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq30320
       have i₂ := eq26900 (σ (M.op x x)) (σ x)
       grind)
    | exact superpose eq26900 eq30320
    | exact resolve eq30320 eq26900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26900 eq30320
  have eq30467 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq30344
       have i₂ := eq26885 (M.op (σ y) (σ x))
       grind)
    | exact superpose eq26885 eq30344
    | exact resolve eq30344 eq26885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30344
  have eq30832 : (τ y) = (M.op (τ x) (M.op (M.op (τ (M.op x x)) (τ y)) (τ x))) := by
    first
    | (have i₁ := eq27032 (M.op (M.op (τ (M.op x x)) (τ y)) (τ x))
       have i₂ := eq23702 (τ (M.op x x))
       grind)
    | exact superpose eq23702 eq27032
    | exact resolve eq27032 eq23702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23702
  have eq30849 : (τ y) = (M.op (τ (M.op x x)) (M.op (τ y) (τ x))) := by
    first
    | (have i₁ := eq30832
       have i₂ := eq27055 (τ (M.op x x)) (τ x)
       grind)
    | exact superpose eq27055 eq30832
    | exact resolve eq30832 eq27055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27055 eq30832
  have eq30976 : (τ y) = (M.op (τ x) (M.op (τ y) (τ x))) := by
    first
    | (have i₁ := eq30849
       have i₂ := eq27032 (M.op (τ y) (τ x))
       grind)
    | exact superpose eq27032 eq30849
    | exact resolve eq30849 eq27032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27032 eq30849
  have eq31135 : (σ (M.op (τ y) (τ x))) = (M.op (σ (M.op (τ y) (τ x))) (σ (M.op (M.op (M.op (τ y) (τ x)) (τ x)) (τ y)))) := by
    first
    | (have i₁ := eq2036 (M.op (τ y) (τ x)) (τ x)
       have i₂ := eq30976
       grind)
    | exact superpose eq30976 eq2036
    | exact resolve eq2036 eq30976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2036 eq30976
  have eq31143 : (σ (M.op (τ y) (τ x))) = (M.op (σ (M.op (τ y) (τ x))) (σ (M.op (M.op (M.op (τ x) (τ x)) (τ y)) (τ y)))) := by
    first
    | (have i₁ := eq31135
       have i₂ := eq1843 (τ x) (τ x) (τ y) (τ y)
       grind)
    | (have i₁ := eq31135
       have i₂ := eq1843 (τ x) (τ y) (τ x) (τ y)
       grind)
    | exact superpose eq1843 eq31135
    | exact resolve eq31135 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843 eq31135
  have eq31155 : (σ (M.op (τ y) (τ x))) = (M.op (σ (M.op (τ y) (τ x))) (σ (M.op (τ x) (M.op (τ x) (τ (M.op x x)))))) := by
    first
    | (have i₁ := eq31143
       have i₂ := eq26971 (τ x) (τ x)
       grind)
    | exact superpose eq26971 eq31143
    | exact resolve eq31143 eq26971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26971 eq31143
  have eq31163 : (σ (M.op (τ y) (τ x))) = (M.op (σ (M.op (τ y) (τ x))) (σ (τ (M.op x (M.op x (M.op x x)))))) := by
    first
    | (have i₁ := eq31155
       have i₂ := eq394 x
       grind)
    | exact superpose eq394 eq31155
    | exact resolve eq31155 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394 eq31155
  have eq31168 : (σ (M.op (τ y) (τ x))) = (M.op (σ (M.op (τ y) (τ x))) (M.op x (M.op x (M.op x x)))) := by
    first
    | (have i₁ := eq31163
       have i₂ := eq11 (M.op x (M.op x (M.op x x)))
       grind)
    | exact superpose eq11 eq31163
    | exact resolve eq31163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31163
  have eq31172 : (σ (M.op (τ y) (τ x))) = (M.op x (M.op x (M.op x (M.op (σ (M.op (τ y) (τ x))) x)))) := by
    first
    | (have i₁ := eq31168
       have i₂ := eq5963 x x x (σ (M.op (τ y) (τ x))) x
       grind)
    | (have i₁ := eq31168
       have i₂ := eq5963 x (σ (M.op (τ y) (τ x))) x x x
       grind)
    | exact superpose eq5963 eq31168
    | exact resolve eq31168 eq5963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5963 eq31168
  have eq31175 : (σ (M.op (τ y) (τ x))) = (M.op (σ (M.op (τ y) (τ x))) x) := by
    first
    | (have i₁ := eq31172
       have i₂ := eq26063 (M.op (σ (M.op (τ y) (τ x))) x)
       grind)
    | exact superpose eq26063 eq31172
    | exact resolve eq31172 eq26063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26063 eq31172
  have eq39005 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x x) y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26885 (σ y)
       have i₂ := eq23726 (M.op x x)
       grind)
    | exact superpose eq23726 eq26885
    | (have j1 := eq23726 (M.op x x)
       grind)
    | exact resolve eq26885 eq23726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23726 eq26885
  have eq39122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39005
       have i₂ := eq23977 y
       grind)
    | exact superpose eq23977 eq39005
    | exact resolve eq39005 eq23977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23977 eq39005
  have eq39141 : x = (M.op x x) := by
    first
    | (have r₁ := eq39122
       have r₂ := eq16
       grind)
    | exact resolve eq39122 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39122
  have eq39158 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq23769
       have i₂ := eq39141
       grind)
    | exact superpose eq39141 eq23769
    | exact resolve eq23769 eq39141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23769
  have eq39159 : (τ y) = (M.op (τ y) (τ x)) := by
    first
    | (have i₁ := eq23771
       have i₂ := eq39141
       grind)
    | exact superpose eq39141 eq23771
    | exact resolve eq23771 eq39141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23771 eq39141
  have eq39694 : (σ (τ y)) = (M.op (σ (τ y)) x) := by
    first
    | (have i₁ := eq31175
       have i₂ := eq39159
       grind)
    | exact superpose eq39159 eq31175
    | exact resolve eq31175 eq39159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31175 eq39159
  have eq39711 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30467
       have i₂ := eq39158
       grind)
    | exact superpose eq39158 eq30467
    | exact resolve eq30467 eq39158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30467 eq39158
  have eq39856 : y = (M.op y x) := by
    first
    | (have i₁ := eq39694
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq39694
    | exact resolve eq39694 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39694
  have eq39893 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39711
       grind)
    | exact superpose eq39711 eq16
    | exact resolve eq16 eq39711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39711
  have eq39975 : y = (M.op x y) := by
    first
    | (have i₁ := eq23939
       have i₂ := eq39856
       grind)
    | exact superpose eq39856 eq23939
    | exact resolve eq23939 eq39856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23939 eq39856
  have eq40246 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq39893
       have i₂ := eq39975
       grind)
    | exact superpose eq39975 eq39893
    | exact resolve eq39893 eq39975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39893 eq39975
  have eq40256 : False := by grind
  exact eq40256

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_x_pxy_pxx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq30 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq91 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X2
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq125 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq125 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq125
    | (have j0 := eq125 (σ X0) (σ X1)
       grind)
    | exact resolve eq125 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq91 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq91
    | exact resolve eq91 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq177 : ∀ X1 X3 X4 : G, (M.op (M.op X1 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X1 X3 X4
    first
    | (have i₁ := eq29 X3 x (M.op (M.op x x) (M.op X1 X1)) X4
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq29
    | exact resolve eq29 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq211 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq140 X1 (M.op x (M.op x x))
       have i₂ := eq177 x x x
       grind)
    | exact superpose eq177 eq140
    | exact resolve eq140 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq266 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq134 x y
       grind)
    | exact superpose eq134 eq16
    | (have j1 := eq134 x y
       grind)
    | exact resolve eq16 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq729 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99 X0 (M.op X0 X0) X2 X1
       have i₂ := eq211 X0 X0
       grind)
    | exact superpose eq211 eq99
    | exact resolve eq99 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq731 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq99 X0 X0 x (M.op X0 X0)
       have i₂ := eq177 x X0 X0
       grind)
    | exact superpose eq177 eq99
    | exact resolve eq99 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq761 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq731 (σ X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq731
    | exact resolve eq731 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq873 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1)))) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99 (M.op X0 X1) X1 X3 X2
       have i₂ := eq729 X1 X1 X0
       grind)
    | exact superpose eq729 eq99
    | exact resolve eq99 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq884 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq873 X0 X1 x x
       have i₂ := eq99 X1 X1 x x
       grind)
    | exact superpose eq99 eq873
    | exact resolve eq873 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq873
  have eq1564 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq266
       have i₂ := eq125 x y
       grind)
    | exact superpose eq125 eq266
    | (have j1 := eq125 (σ x) (σ y)
       grind)
    | exact resolve eq266 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq266
  have eq1565 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1564
  have eq1579 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq884 (σ x) (σ y)
       have i₂ := eq1565
       grind)
    | exact superpose eq1565 eq884
    | exact resolve eq884 eq1565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1583 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1579
       have i₂ := eq60 y
       grind)
    | exact superpose eq60 eq1579
    | exact resolve eq1579 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1579
  have eq11230 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1565
       have i₂ := eq1583
       grind)
    | exact superpose eq1583 eq1565
    | exact resolve eq1565 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565 eq1583
  have eq11282 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq11230
  have eq11326 : (M.op y y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq11282
       grind)
    | exact superpose eq11282 eq10
    | exact resolve eq10 eq11282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11282
  have eq11366 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11326
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11326
    | exact resolve eq11326 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11326
  have eq11480 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq884 y y
       have i₂ := eq11366
       grind)
    | exact superpose eq11366 eq884
    | exact resolve eq884 eq11366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11366
  have eq11499 : x = (M.op x y) := by grind
  clear eq11480
  have eq11595 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq884 x y
       have i₂ := eq11499
       grind)
    | exact superpose eq11499 eq884
    | exact resolve eq884 eq11499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq11624 : x = (M.op y y) := by
    first
    | (have i₁ := eq11595
       have i₂ := eq11499
       grind)
    | exact superpose eq11499 eq11595
    | exact resolve eq11595 eq11499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11595
  have eq11683 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq761 y
       have i₂ := eq11624
       grind)
    | exact superpose eq11624 eq761
    | exact resolve eq761 eq11624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761 eq11624
  have eq12107 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11683
       grind)
    | exact superpose eq11683 eq16
    | exact resolve eq16 eq11683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11683
  have eq12161 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq12107
       have i₂ := eq11499
       grind)
    | exact superpose eq11499 eq12107
    | exact resolve eq12107 eq11499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11499 eq12107
  have eq12162 : False := by grind
  exact eq12162

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyx_y_pyy_x_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq64 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq43
    | exact resolve eq43 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
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
  clear eq44
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq249 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq51 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq66 (τ X0)
       grind)
    | exact superpose eq66 eq34
    | exact resolve eq34 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq323 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq312 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq312
    | exact resolve eq312 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq326 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq323 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq323
    | exact resolve eq323 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq323
  have eq529 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq570 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
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
  have eq593 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
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
  have eq608 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq614 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq609 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq609
    | exact resolve eq609 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq615 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq608 X0 X1 X2 X3
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq608
    | exact resolve eq608 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq649 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq53 (σ X0) (σ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq53
    | exact resolve eq53 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq14
    | exact resolve eq14 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq649 X0
       have i₂ := eq73 (M.op X0 X0)
       grind)
    | exact superpose eq73 eq649
    | exact resolve eq649 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq649
  have eq670 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq661 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq661
    | exact resolve eq661 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq817 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq326 X0
       grind)
    | exact superpose eq326 eq16
    | exact resolve eq16 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq969 : ∀ X0 : G, (τ X0) = (M.op y (M.op (M.op x y) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq817 X0
       grind)
    | exact superpose eq817 eq50
    | exact resolve eq50 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq1942 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq249 eq570
    | exact resolve eq570 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq1986 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq570 X0 X0 X0
       grind)
    | exact superpose eq570 eq14
    | exact resolve eq14 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1987 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq570 X0 X0 X0
       grind)
    | exact superpose eq570 eq50
    | exact resolve eq50 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1988 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq570 X0 X0 X0
       grind)
    | exact superpose eq570 eq51
    | exact resolve eq51 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1998 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq603 (M.op x (M.op x x)) x
       have i₂ := eq570 x x x
       grind)
    | exact superpose eq570 eq603
    | exact resolve eq603 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq603
  have eq2212 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq529 X0
       have i₂ := eq1987 X0
       grind)
    | exact superpose eq1987 eq529
    | exact resolve eq529 eq1987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2416 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq529 X0
       have i₂ := eq1988 X0
       grind)
    | exact superpose eq1988 eq529
    | exact resolve eq529 eq1988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529 eq1988
  have eq2732 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq26 eq1998
    | (have j0 := eq1998 (σ y) (σ x)
       grind)
    | exact resolve eq1998 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998
  have eq2798 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq2732
       have i₂ := eq1987 sF3
       grind)
    | exact superpose eq1987 eq2732
    | exact resolve eq2732 eq1987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732
  have eq3002 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | exact superpose eq969 eq2212
    | exact resolve eq2212 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969 eq2212
  have eq6327 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq615 X0 X1 X2 X3
       have i₂ := eq614 X0 X1
       grind)
    | exact superpose eq614 eq615
    | exact resolve eq615 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq615
  have eq6529 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6327 (M.op X3 (M.op X2 X1)) (M.op X0 X0) X1 X2
       have i₂ := eq14 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq14 eq6327
    | exact resolve eq6327 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6327
  have eq29689 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq593 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq1986 X0 X0 X1
       grind)
    | exact superpose eq1986 eq593
    | exact resolve eq593 eq1986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986
  have eq29776 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq29689 X0 X1 x x x
       have i₂ := eq593 X0 X0 x x x
       grind)
    | exact superpose eq593 eq29689
    | exact resolve eq29689 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq29689
  have eq37010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37011 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq37010
    | exact resolve eq37010 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37010
  have eq37022 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq37011
       have r₂ := eq27
       grind)
    | exact resolve eq37011 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37011
  have eq37026 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq37022
    | exact resolve eq37022 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37022
  have eq37030 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq37026 eq64
    | (have r₁ := eq64
       have r₂ := eq37026
       grind)
    | exact resolve eq64 eq37026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq37143 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq37026 eq29776
    | exact resolve eq29776 eq37026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37026
  have eq37145 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq37030
  have eq37196 : (σ x) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq37143 eq2416
    | exact resolve eq2416 eq37143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416 eq37143
  have eq37750 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq37145 eq97
    | exact resolve eq97 eq37145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq37145
  have eq37763 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq37750
  have eq38210 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq37763 eq29776
    | exact resolve eq29776 eq37763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42400 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq38210 eq37763
    | exact resolve eq37763 eq38210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37763 eq38210
  have eq42444 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq42400
  have eq42525 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq42444 eq3002
    | exact resolve eq3002 eq42444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3002 eq42444
  have eq42595 : (τ (σ y)) = (M.op (τ (σ y)) x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq28 eq42525
    | exact resolve eq42525 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq42525
  have eq42632 : y = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq29 eq42595
    | exact resolve eq42595 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq42595
  have eq42633 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq42632
  have eq42724 : (M.op (σ y) (σ (M.op x y))) = (M.op y (M.op (M.op x y) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq42633 eq1987
    | exact resolve eq1987 eq42633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1987
  have eq42742 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq42633 eq53
    | exact resolve eq53 eq42633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47618 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ (M.op x y)))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq42724 eq2798
    | exact resolve eq2798 eq42724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2798 eq42724
  have eq47687 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq42742 eq47618
    | exact resolve eq47618 eq42742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42742 eq47618
  have eq47738 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq47687
  have eq47765 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq47738 eq1942
    | exact resolve eq1942 eq47738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942 eq47738
  have eq58641 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq37196 eq47765
    | exact resolve eq47765 eq37196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37196 eq47765
  have eq58702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq58641
  have eq58715 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq58702
    | exact resolve eq58702 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58702
  have eq58720 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq58715
       have r₂ := eq27
       grind)
    | exact resolve eq58715 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58715
  have eq58730 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq58720 eq53
    | exact resolve eq53 eq58720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq58720
  have eq58800 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq58730
    | exact resolve eq58730 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58730
  have eq58823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq58800 eq42633
    | exact resolve eq42633 eq58800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42633 eq58800
  have eq58981 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq58823
  have eq59028 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq58981
       have r₂ := eq27
       grind)
    | exact resolve eq58981 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58981
  have eq59998 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq59028
       grind)
    | exact superpose eq59028 eq72
    | exact resolve eq72 eq59028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq60030 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) (M.op X0 X0))) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq651 x X0
       have i₂ := eq59028
       grind)
    | exact superpose eq59028 eq651
    | exact resolve eq651 eq59028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq60202 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) (M.op X0 X0))) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq20 eq60030
    | (have j0 := eq60030 X0
       grind)
    | exact resolve eq60030 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60030
  have eq60222 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq59998
    | exact resolve eq59998 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59998
  have eq60250 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) (M.op X0 X0))) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq60202 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq60202
    | (have j0 := eq60202 X0
       grind)
    | exact resolve eq60202 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60202
  have eq71806 : x = (M.op (σ x) (M.op (σ (M.op x y)) (M.op x y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq60250 x
       have i₂ := eq59028
       grind)
    | exact superpose eq59028 eq60250
    | exact resolve eq60250 eq59028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71909 : x = (M.op (σ x) (M.op (σ (M.op x y)) (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq71806
  have eq76935 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0)))) = (M.op x X0) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq6529 X0 x x X1
       have i₂ := eq59028
       grind)
    | exact superpose eq59028 eq6529
    | exact resolve eq6529 eq59028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6529 eq59028
  have eq77601 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq76935 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq76935
    | exact resolve eq76935 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76935
  have eq78011 : y = (M.op (σ x) (M.op (σ (M.op x y)) (M.op x y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq60250 y
       have i₂ := eq77601 y
       grind)
    | exact superpose eq77601 eq60250
    | exact resolve eq60250 eq77601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60250 eq77601
  have eq78201 : y = (M.op (σ x) (M.op (σ (M.op x y)) (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq78011
  have eq78305 : y = (M.op (σ x) (M.op (σ (M.op x y)) (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq78201
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78201
    | exact resolve eq78201 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78201
  have eq80449 : x = y ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq78305 eq71909
    | exact resolve eq71909 eq78305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71909 eq78305
  have eq80517 : y = (M.op y x) ∨ x = y := by grind
  clear eq80449
  have eq80643 : (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq29776 x y
       have i₂ := eq80517
       grind)
    | exact superpose eq80517 eq29776
    | exact resolve eq29776 eq80517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29776
  have eq82487 : y = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq80517
       have i₂ := eq80643
       grind)
    | exact superpose eq80643 eq80517
    | exact resolve eq80517 eq80643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80517 eq80643
  have eq82555 : y = (M.op x x) ∨ x = y := by grind
  clear eq82487
  have eq82613 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq670 x
       have i₂ := eq82555
       grind)
    | exact superpose eq82555 eq670
    | exact resolve eq670 eq82555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq82555
  have eq82822 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq82613
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq82613
    | exact resolve eq82613 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82613
  have eq82885 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq82822
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq82822
    | exact resolve eq82822 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82822
  have eq82912 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq82885
    | exact resolve eq82885 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82885
  have eq82925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq82912
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82912
    | exact resolve eq82912 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82912
  have eq82930 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq82925
    | exact resolve eq82925 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82925
  have eq82931 : x = y := by
    first
    | (have r₁ := eq82930
       have r₂ := eq27
       grind)
    | exact resolve eq82930 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82930
  have eq83123 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq82931
       grind)
    | exact superpose eq82931 eq18
    | exact resolve eq18 eq82931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq83124 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq82931
       grind)
    | exact superpose eq82931 eq24
    | exact resolve eq24 eq82931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq83420 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq83124
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq83124
    | exact resolve eq83124 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83124
  have eq83468 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq83420 eq26
    | exact resolve eq26 eq83420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq83420
  have eq84241 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq83468 eq71
    | exact resolve eq71 eq83468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq84255 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq83468 eq60222
    | exact resolve eq60222 eq83468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60222 eq83468
  have eq84521 : y = (M.op y x) := by
    first
    | (have r₁ := eq84255
       have r₂ := eq27
       grind)
    | exact resolve eq84255 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84255
  have eq84534 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq84241
       have i₂ := eq83123
       grind)
    | exact superpose eq83123 eq84241
    | exact resolve eq84241 eq83123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84241
  have eq84588 : x = (M.op x x) := by
    first
    | (have i₁ := eq84521
       have i₂ := eq82931
       grind)
    | exact superpose eq82931 eq84521
    | exact resolve eq84521 eq82931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82931 eq84521
  have eq84623 : x = (M.op x y) := by
    first
    | (have i₁ := eq84588
       have i₂ := eq83123
       grind)
    | exact superpose eq83123 eq84588
    | exact resolve eq84588 eq83123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83123 eq84588
  have eq84655 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq84623 eq20
    | exact resolve eq20 eq84623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq85109 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq84655
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq84655
    | exact resolve eq84655 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84655
  have eq85930 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq84623 eq84534
    | exact resolve eq84534 eq84623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84534 eq84623
  have eq85938 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq85930 eq15
    | exact resolve eq15 eq85930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85930
  have eq86052 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85938
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85938
    | exact resolve eq85938 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq85938
  have eq86098 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq85109 eq86052
    | exact resolve eq86052 eq85109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85109 eq86052
  have eq86141 : False := by grind
  exact eq86141

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyy_x_pxx_pxx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
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
  have eq62 : ∀ X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq75 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq62 (M.op x x)
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) (k (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq19
    | exact resolve eq19 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq90 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq98 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq90
    | exact resolve eq90 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq90
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq98 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98
    | exact resolve eq98 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq25 X0 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq25
    | exact resolve eq25 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (k (M.op X0 (M.op X1 X0)) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (M.op X1 X0)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq76
    | exact resolve eq76 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (M.op (M.op X1 x) (M.op (M.op X1 x) (M.op X1 x)))
       have i₂ := eq24 (M.op X1 x) X1 x (M.op X1 x)
       grind)
    | exact superpose eq24 eq62
    | exact resolve eq62 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 X2) (M.op (M.op X1 X2) (M.op X1 X2))) X1
       have i₂ := eq24 (M.op X1 X2) X1 X2 (M.op X1 X2)
       grind)
    | exact superpose eq24 eq12
    | (have r₁ := eq12 (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op (M.op X1 X2) (M.op X0 X0))) (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op (M.op X1 X2) (M.op X0 X0)))))
       have r₂ := eq24 X0 X1 X2 (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op (M.op X1 X2) (M.op X0 X0)))
       grind)
    | exact resolve eq12 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq24 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq169 X0 X1 X2 X3
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq169
    | exact resolve eq169 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq175 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) X2) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq168 X0 X1 X2
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq168
    | (have j0 := eq168 X0 X1 X2
       grind)
    | exact resolve eq168 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq176 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X0 X1
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq167
    | exact resolve eq167 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq185 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) X2) ∨ (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X0 X1 X2
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq175
    | (have j0 := eq175 X0 X1 X2
       grind)
    | exact resolve eq175 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq194 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq76 (σ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq76
    | exact resolve eq76 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq197 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq9
    | exact resolve eq9 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq9
    | exact resolve eq9 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq194 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq194
    | exact resolve eq194 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq262 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (k (M.op X1 X1) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X1 (M.op X2 (M.op X0 X0)) (M.op (M.op x x) (M.op X2 X2))
       have i₂ := eq24 X2 x x X0
       grind)
    | exact superpose eq24 eq80
    | exact resolve eq80 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq297 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (k (k (M.op X0 X0) X0) (M.op X0 X0))) (M.op (k (M.op X0 X0) X0) (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 (k (M.op X0 X0) X0) X1 X2 X3
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq24
    | exact resolve eq24 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 X0) X0) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 (k (k (M.op X0 X0) X0) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X3 X1 X2 (k (M.op X0 X0) X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq24
    | exact resolve eq24 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq102 X1
       grind)
    | exact superpose eq102 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq345 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq344 X0 X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq344
    | (have j0 := eq344 X0 X1
       grind)
    | exact resolve eq344 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq386 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq345 x y
       grind)
    | exact superpose eq345 eq16
    | (have j1 := eq345 x y
       grind)
    | exact resolve eq16 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq345 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq548 : ∀ X0 X2 X3 : G, (M.op (M.op X0 (M.op X2 X2)) (M.op X2 (M.op X3 X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq24 X2 (σ x) (M.op (σ (M.op x x)) (M.op X0 X0)) X3
       have i₂ := eq201 x X0
       grind)
    | exact superpose eq201 eq24
    | exact resolve eq24 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq770 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq548 X1 X0 (M.op X0 X0)
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq548
    | exact resolve eq548 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq548 X0 X0 X0
       have i₂ := eq25 X0 (M.op X0 X0)
       grind)
    | exact superpose eq25 eq548
    | exact resolve eq548 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq548 X0 X0 X0
       grind)
    | exact superpose eq548 eq9
    | exact resolve eq9 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq825 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq118 (σ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq118
    | exact resolve eq118 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq770 (M.op x (M.op x x)) X1
       have i₂ := eq548 x x x
       grind)
    | exact superpose eq548 eq770
    | exact resolve eq770 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq963 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq75
    | exact resolve eq75 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq969 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq206 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq206
    | exact resolve eq206 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq979 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq963 X0
       have i₂ := eq25 X0 (M.op X0 X0)
       grind)
    | exact superpose eq25 eq963
    | exact resolve eq963 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq990 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq979 X0
       have i₂ := eq775 X0
       grind)
    | exact superpose eq775 eq979
    | exact resolve eq979 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq1251 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (σ (M.op (M.op (τ X0) (τ X0)) (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq969 (M.op (τ X0) (τ X0))
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq969
    | exact resolve eq969 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1253 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) (k (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq969 (M.op X0 X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq969
    | exact resolve eq969 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq1282 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq1253 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq1253
    | exact resolve eq1253 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1284 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (σ (M.op (M.op (τ X0) (τ X0)) (k (M.op (τ X0) (τ X0)) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq1251 X0
       have i₂ := eq62 (τ X0)
       grind)
    | exact superpose eq62 eq1251
    | exact resolve eq1251 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1292 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1282 X0
       have i₂ := eq775 X0
       grind)
    | exact superpose eq775 eq1282
    | exact resolve eq1282 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq1293 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (M.op (τ X0) (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq1284 X0
       have i₂ := eq117 (τ X0)
       grind)
    | exact superpose eq117 eq1284
    | exact resolve eq1284 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1297 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1293 X0
       have i₂ := eq775 (τ X0)
       grind)
    | exact superpose eq775 eq1293
    | exact resolve eq1293 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq1298 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1297 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1297
    | exact resolve eq1297 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq1465 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq386
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq386
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq386 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq1466 : (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1465
  have eq1527 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq408 (τ X0) (τ X1)
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq408
    | (have j0 := eq408 (τ X0) (τ X1)
       grind)
    | exact resolve eq408 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq408
  have eq1553 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1527 X0 X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq1527
    | (have j0 := eq1527 X0 X1
       grind)
    | exact resolve eq1527 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1527
  have eq1567 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1553 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1553
    | (have j0 := eq1553 X0 X1
       grind)
    | exact resolve eq1553 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq1577 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1567 X0 X1
       have i₂ := eq98 X1
       grind)
    | exact superpose eq98 eq1567
    | (have j0 := eq1567 X0 X1
       grind)
    | exact resolve eq1567 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567
  have eq1582 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1577 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1577
    | (have j0 := eq1577 X0 X1
       grind)
    | exact resolve eq1577 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1577
  have eq1585 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1582 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1582
    | (have j0 := eq1582 X0 X1
       grind)
    | exact resolve eq1582 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1582
  have eq1586 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1585 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1585
    | (have j0 := eq1585 X0 X1
       grind)
    | exact resolve eq1585 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585
  have eq1587 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1586 X0 X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq1586
    | (have j0 := eq1586 X0 X1
       grind)
    | exact resolve eq1586 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq1586
  have eq2179 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq118 X2
       have i₂ := eq781 X2 X0 X1
       grind)
    | exact superpose eq781 eq118
    | exact resolve eq118 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq2182 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq841 X2 X3
       have i₂ := eq781 X2 X0 X1
       grind)
    | exact superpose eq781 eq841
    | exact resolve eq841 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2209 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq123 X0 (M.op X1 X0) X2 X3
       have i₂ := eq781 X0 X0 X1
       grind)
    | exact superpose eq781 eq123
    | exact resolve eq123 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2228 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2209 X0 X1 x x
       have i₂ := eq123 X0 X0 x x
       grind)
    | exact superpose eq123 eq2209
    | exact resolve eq2209 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2209
  have eq2464 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2179 (M.op X2 (M.op X0 X0)) (M.op x (M.op X2 X2)) X1
       have i₂ := eq548 x X2 X0
       grind)
    | exact superpose eq548 eq2179
    | exact resolve eq2179 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq3127 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) = (M.op (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) (k (M.op X0 X1) (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq120 (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1)))
       have i₂ := eq123 X1 X0 (M.op X1 (M.op X0 X1)) X2
       grind)
    | exact superpose eq123 eq120
    | exact resolve eq120 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq3236 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) = (M.op (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) (k (M.op X0 X1) (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3127 X0 X1 X1
       have i₂ := eq2228 (M.op X1 (M.op X0 X1)) X1
       grind)
    | exact superpose eq2228 eq3127
    | exact resolve eq3127 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3127
  have eq3249 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3236 X0 X0
       have i₂ := eq25 X0 (M.op X0 X0)
       grind)
    | exact superpose eq25 eq3236
    | exact resolve eq3236 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3236
  have eq3740 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0) = (M.op (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2179 (M.op X3 X0) X2 (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0)
       have i₂ := eq2182 (M.op X2 (M.op X3 X0)) X1 X0 X3
       grind)
    | exact superpose eq2182 eq2179
    | exact resolve eq2179 eq2182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2179
  have eq3770 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3740 X0 X1 X2 X3
       have i₂ := eq2228 X0 (M.op X1 (M.op X2 (M.op X3 X0)))
       grind)
    | exact superpose eq2228 eq3740
    | exact resolve eq3740 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228 eq3740
  have eq3827 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq262 X0 X1 X2
       have i₂ := eq117 X1
       grind)
    | exact superpose eq117 eq262
    | exact resolve eq262 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq4071 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) X0) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 (M.op (M.op X0 X0) (k (M.op X0 X0) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3827 X0 (M.op X1 X1) X2
       have i₂ := eq62 X1
       grind)
    | exact superpose eq62 eq3827
    | exact resolve eq3827 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3827
  have eq4181 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4071 X0 X1 X2
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq4071
    | exact resolve eq4071 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4071
  have eq4204 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4181 X0 X1 X2
       have i₂ := eq775 X0
       grind)
    | exact superpose eq775 eq4181
    | exact resolve eq4181 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq4181
  have eq6090 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) = (M.op (M.op X3 (M.op X2 X3)) (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq174 X1 (M.op X0 X1) X1 X0
       have i₂ := eq174 X0 X1 X2 X3
       grind)
    | exact superpose eq174 eq174
    | exact resolve eq174 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6100 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) = (M.op (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq174 (M.op X4 (M.op X3 X2)) (M.op X0 X1) X2 X3
       have i₂ := eq174 X0 X1 (M.op X3 X2) X4
       grind)
    | exact superpose eq174 eq174
    | exact resolve eq174 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6407 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6090 X0 X1 X2 X3
       have i₂ := eq2182 X0 X1 (M.op X2 X3) X3
       grind)
    | exact superpose eq2182 eq6090
    | exact resolve eq6090 eq2182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2182 eq6090
  have eq8741 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3770 (M.op X1 X0) X2 X0 (M.op x (M.op X1 X1))
       have i₂ := eq2464 X1 X0 x
       grind)
    | exact superpose eq2464 eq3770
    | exact resolve eq3770 eq2464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770
  have eq8895 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8741 X0 X1 X2
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq8741
    | exact resolve eq8741 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8741
  have eq13016 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (k (M.op X0 (M.op X0 X0)) (M.op X0 X0))) (M.op (M.op X0 (M.op X0 X0)) (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq297 X0 X1 X2 X3
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq297
    | exact resolve eq297 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq13017 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13016 X0 X1 X2 X3
       have i₂ := eq990 X0
       grind)
    | exact superpose eq990 eq13016
    | exact resolve eq13016 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13016
  have eq13194 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (M.op X1 (M.op X1 X1)) (M.op X0 X0) X1 (M.op x x)
       have i₂ := eq13017 X1 x x X0
       grind)
    | exact superpose eq13017 eq174
    | exact resolve eq174 eq13017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq13017
  have eq13782 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq298 X0 X1 X2 X3
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq298
    | exact resolve eq298 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq13783 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13782 X0 X1 X2 X3
       have i₂ := eq990 X0
       grind)
    | exact superpose eq990 eq13782
    | exact resolve eq13782 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990 eq13782
  have eq16442 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (k (τ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) X2) ∨ (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) X2
       have i₂ := eq185 X0 X1 (σ X2)
       grind)
    | exact superpose eq185 eq23
    | (have j1 := eq185 X0 X1 (σ X2)
       grind)
    | exact resolve eq23 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq185
  have eq20441 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6407 (M.op X1 X1) (M.op x x) X1 (M.op X0 X0)
       have i₂ := eq24 X1 x x X0
       grind)
    | exact superpose eq24 eq6407
    | exact resolve eq6407 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq20661 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20441 X0 X1
       have i₂ := eq8895 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq8895 eq20441
    | exact resolve eq20441 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20441
  have eq22185 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20661 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq13783 X0 X1 X1 X1
       grind)
    | exact superpose eq13783 eq20661
    | exact resolve eq20661 eq13783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13783
  have eq22200 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X2 (M.op X1 X1)) X0) (M.op (M.op X2 (M.op X1 X1)) X0))) = (M.op (M.op (M.op X2 (M.op X1 X1)) X0) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20661 (M.op (M.op X2 (M.op X1 X1)) X0) X1
       have i₂ := eq781 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq781 eq20661
    | exact resolve eq20661 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq22549 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X2 (M.op X1 X1)) X0) (M.op (M.op X2 (M.op X1 X1)) X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22200 X0 X1 X2
       have i₂ := eq841 X0 (M.op X2 (M.op X1 X1))
       grind)
    | exact superpose eq841 eq22200
    | exact resolve eq22200 eq841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22200
  have eq22564 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22185 X0 X1
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq22185
    | exact resolve eq22185 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22185
  have eq22673 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X1 X1)) X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22549 X0 X1 X2
       have i₂ := eq25 (M.op X2 (M.op X1 X1)) X0
       grind)
    | exact superpose eq25 eq22549
    | exact resolve eq22549 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22549
  have eq22688 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22564 X0 X1
       have i₂ := eq841 X0 X1
       grind)
    | exact superpose eq841 eq22564
    | exact resolve eq22564 eq841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq22564
  have eq23033 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op X1 X0)) (M.op X1 X1)
       have i₂ := eq22688 X0 X1
       grind)
    | exact superpose eq22688 eq9
    | exact resolve eq9 eq22688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22688
  have eq28371 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6407 (M.op X2 X1) X1 X1 (M.op X0 X0)
       have i₂ := eq23033 X1 X2 X0
       grind)
    | exact superpose eq23033 eq6407
    | exact resolve eq6407 eq23033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6407 eq23033
  have eq28671 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28371 X0 X1 X2
       have i₂ := eq8895 X0 (M.op X2 X1) X0
       grind)
    | exact superpose eq8895 eq28371
    | exact resolve eq28371 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8895 eq28371
  have eq29851 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq123 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X3 X2
       have i₂ := eq22673 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq22673 eq123
    | exact resolve eq123 eq22673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq22673
  have eq29909 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29851 X0 X1 X2 X3
       have i₂ := eq25 X2 X3
       grind)
    | exact superpose eq25 eq29851
    | exact resolve eq29851 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29851
  have eq121413 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13194 X0 X1
       have i₂ := eq20661 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) X0
       grind)
    | exact superpose eq20661 eq13194
    | exact resolve eq13194 eq20661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13194 eq20661
  have eq121414 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq121413 X0 X1
       have i₂ := eq25 (M.op X1 (M.op X1 X1)) (M.op X0 X0)
       grind)
    | exact superpose eq25 eq121413
    | exact resolve eq121413 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121413
  have eq121415 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X1) (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq121414 X0 X1
       have i₂ := eq28671 (M.op X0 X0) (M.op X1 X1) X1
       grind)
    | exact superpose eq28671 eq121414
    | exact resolve eq121414 eq28671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121414
  have eq121416 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X1) (k (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq121415 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq121415
    | exact resolve eq121415 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq121415
  have eq121417 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq121416 X0 X1
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq121416
    | exact resolve eq121416 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq121416
  have eq121516 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X2 (M.op (M.op X3 X3) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq121417 X2 X3
       have i₂ := eq4204 X2 X0 X1
       grind)
    | exact superpose eq4204 eq121417
    | exact resolve eq121417 eq4204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121417
  have eq128054 : (M.op y y) = (τ (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1466
       grind)
    | exact superpose eq1466 eq10
    | exact resolve eq10 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq128157 : x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq128054
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq128054
    | exact resolve eq128054 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128054
  have eq128158 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op y y) := by grind
  clear eq128157
  have eq169596 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X1 (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3249 X0 X1
       have i₂ := eq29909 (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq29909 eq3249
    | exact resolve eq3249 eq29909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3249
  have eq169597 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X1 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq169596 X0 X1
       have i₂ := eq176 X0 X1
       grind)
    | exact superpose eq176 eq169596
    | exact resolve eq169596 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq169596
  have eq177844 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (k (τ (M.op X1 (M.op X1 (M.op X0 X1)))) X2) ∨ (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16442 X0 X1 X2
       have i₂ := eq169597 X0 X1
       grind)
    | exact superpose eq169597 eq16442
    | (have j0 := eq16442 X0 X1 X2
       grind)
    | exact resolve eq16442 eq169597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16442
  have eq177845 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 (σ X2)) ∨ (τ (M.op X0 X1)) = (k (τ (M.op X1 (M.op X1 (M.op X0 X1)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177844 X0 X1 X2
       have i₂ := eq29909 (σ X2) (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq29909 eq177844
    | (have j0 := eq177844 X0 X1 X2
       grind)
    | (have r₁ := eq177844 (σ X2) (σ X2) X2
       have r₂ := eq29909 (σ X2) (M.op (σ X2) (σ X2)) (σ X2) (σ X2)
       grind)
    | exact resolve eq177844 eq29909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29909 eq177844
  have eq178000 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (σ (M.op X0 X0)) ∨ (τ (σ (M.op X0 X0))) = (k (τ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq177845 (σ X0) (σ X0) x
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq177845
    | exact resolve eq177845 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177845
  have eq178156 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq178000 X0 X1
       have i₂ := eq825 X0
       grind)
    | exact superpose eq825 eq178000
    | (have j0 := eq178000 X0 X1
       grind)
    | exact resolve eq178000 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825 eq178000
  have eq178297 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq178156 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq178156
    | (have j0 := eq178156 X0 X1
       grind)
    | exact resolve eq178156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178156
  have eq178421 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq178297 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq178297
    | (have j0 := eq178297 X0 X1
       grind)
    | exact resolve eq178297 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178297
  have eq616041 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) = (M.op X1 (M.op (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)) (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6100 X0 X1 X2 X3 X4
       have i₂ := eq28671 (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)) X1 X0
       grind)
    | exact superpose eq28671 eq6100
    | exact resolve eq6100 eq28671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6100
  have eq616042 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) = (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq616041 X0 X1 X2 X3 X4
       have i₂ := eq25 (M.op X4 (M.op X3 X2)) (M.op X0 X1)
       grind)
    | exact superpose eq25 eq616041
    | exact resolve eq616041 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616041
  have eq616043 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) = (M.op X1 (M.op (M.op X3 X2) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq616042 X0 X1 X2 X3 x
       have i₂ := eq28671 (M.op X0 X1) (M.op X3 X2) x
       grind)
    | exact superpose eq28671 eq616042
    | exact resolve eq616042 eq28671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28671 eq616042
  have eq616044 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) = (M.op X1 (M.op (M.op X3 X2) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq616043 X0 X1 X2 X3
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq616043
    | exact resolve eq616043 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq616043
  have eq616045 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X1 (M.op X0 X1)))) = (M.op X1 (M.op (M.op X3 X2) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq616044 X0 X1 X2 X3
       have i₂ := eq169597 X0 X1
       grind)
    | exact superpose eq169597 eq616044
    | exact resolve eq616044 eq169597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169597 eq616044
  have eq616619 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X4 X3) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)))) = (M.op X3 (M.op X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq616045 X0 X0 X2 X3
       have i₂ := eq4204 X0 X1 X2
       grind)
    | exact superpose eq4204 eq616045
    | exact resolve eq616045 eq4204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4204 eq616045
  have eq618392 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X2 (M.op (M.op X4 X3) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq616619 X0 X1 X2 X3 X4
       have i₂ := eq2464 X1 X2 X0
       grind)
    | exact superpose eq2464 eq616619
    | exact resolve eq616619 eq2464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2464 eq616619
  have eq3646239 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq128158
       grind)
    | exact superpose eq128158 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq128158
       grind)
    | exact resolve eq12 eq128158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128158
  have eq3646966 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op y y) := by grind
  clear eq3646239
  have eq3647285 : (k x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq178421 x y
       grind)
    | (have r₁ := eq3646966
       have r₂ := eq178421 x y
       grind)
    | exact resolve eq3646966 eq178421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178421 eq3646966
  have eq3647572 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1587 x y
       have i₂ := eq3647285
       grind)
    | exact superpose eq3647285 eq1587
    | (have j0 := eq1587 x y
       grind)
    | (have r₁ := eq1587 x y
       have r₂ := eq3647285
       grind)
    | exact resolve eq1587 eq3647285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1587 eq3647285
  have eq3647605 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq3647572
  have eq3647606 : (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq3647605
  have eq3648327 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op X0 (M.op (M.op x x) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) ∨ x = (M.op y y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq618392 X1 X2 X0 y x
       have i₂ := eq3647606
       grind)
    | exact superpose eq3647606 eq618392
    | exact resolve eq618392 eq3647606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618392
  have eq3648419 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq3648327 X0 x x
       have i₂ := eq121516 x x X0 x
       grind)
    | exact superpose eq121516 eq3648327
    | exact resolve eq3648327 eq121516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121516 eq3648327
  have eq3666325 : ∀ X0 : G, x = (M.op x y) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1298 y
       have i₂ := eq3648419 X0
       grind)
    | exact superpose eq3648419 eq1298
    | (have j1 := eq3648419 X0
       grind)
    | exact resolve eq1298 eq3648419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq3667703 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have j0 := eq3648419 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3648419
  have eq3696321 : (M.op x y) = (M.op y y) := by
    first
    | (have j1 := eq3666325 y
       grind)
    | (have r₁ := eq3667703
       have r₂ := eq3666325 x
       grind)
    | exact resolve eq3667703 eq3666325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3666325 eq3667703
  have eq3696348 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op (M.op X1 X0) (σ (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq197 y X0 X1
       have i₂ := eq3696321
       grind)
    | exact superpose eq3696321 eq197
    | exact resolve eq197 eq3696321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3696394 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1292 y
       have i₂ := eq3696321
       grind)
    | exact superpose eq3696321 eq1292
    | exact resolve eq1292 eq3696321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq3771405 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op (M.op X1 X0) (σ (M.op x x)))) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq3696348 X0 X1
       have i₂ := eq3647606
       grind)
    | exact superpose eq3647606 eq3696348
    | exact resolve eq3696348 eq3647606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3647606 eq3696348
  have eq3773975 : (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3771405 x x
       have i₂ := eq197 x x x
       grind)
    | exact superpose eq197 eq3771405
    | exact resolve eq3771405 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq3771405
  have eq3775259 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3773975
       have i₂ := eq3696321
       grind)
    | exact superpose eq3696321 eq3773975
    | exact resolve eq3773975 eq3696321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3696321 eq3773975
  have eq3778223 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3775259
       grind)
    | exact superpose eq3775259 eq10
    | exact resolve eq10 eq3775259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3775259
  have eq3778974 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3778223
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3778223
    | exact resolve eq3778223 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3778223
  have eq3779090 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3778974
       grind)
    | exact superpose eq3778974 eq16
    | exact resolve eq16 eq3778974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3778974
  have eq3779106 : x = (M.op x y) := by
    first
    | (have r₁ := eq3779090
       have r₂ := eq102 x
       grind)
    | exact resolve eq3779090 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq3779090
  have eq3779122 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3696394
       have i₂ := eq3779106
       grind)
    | exact superpose eq3779106 eq3696394
    | exact resolve eq3696394 eq3779106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3696394
  have eq4439744 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3779122
       grind)
    | exact superpose eq3779122 eq16
    | exact resolve eq16 eq3779122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3779122
  have eq4441057 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4439744
       have i₂ := eq3779106
       grind)
    | exact superpose eq3779106 eq4439744
    | exact resolve eq4439744 eq3779106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3779106 eq4439744
  have eq4441058 : False := by grind
  exact eq4441058
