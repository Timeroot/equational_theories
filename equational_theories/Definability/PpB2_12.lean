import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_x_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X2 ∨ (k X3 X2) = (M.op X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq21 X0 X2 X1
       grind)
    | (have i₁ := eq12 X0 (M.op X2 X2)
       have i₂ := eq21 X2 X1 X2
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) (M.op X2 X2))
       have r₂ := eq21 X0 (M.op (M.op X0 X0) (M.op X2 X2)) X2
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq21 X1 X1 X1
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X3 ∨ (M.op X3 X3) = X3 ∨ (k X2 X3) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3
       have i₂ := eq21 X0 X2 X1
       grind)
    | (have i₁ := eq14 (M.op X2 X2) X1
       have i₂ := eq21 X2 X1 X2
       grind)
    | exact superpose eq21 eq14
    | (have j0 := eq14 X3 X3
       grind)
    | exact resolve eq14 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq106 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X3 ∨ (k X2 X3) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq93 X0 X1 X2 X3
       have j1 := eq12 X2 X3
       grind)
    | (have r₁ := eq93 X0 X0 X2 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq93 X0 X1 X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))
       have r₂ := eq12 X0 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | (have r₁ := eq93 X0 X1 X2 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq93 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq112 : ∀ X2 X3 : G, (k X2 X3) = (M.op X3 X2) := by
    intro X2 X3
    first
    | (have j0 := eq106 x x X2 X3
       have j1 := eq91 x x X3 X2
       grind)
    | (have r₁ := eq106 x x X2 X2
       have r₂ := eq91 x x X2 X3
       grind)
    | (have r₁ := eq106 x x X2 (M.op (M.op x x) (M.op x x))
       have r₂ := eq91 x x (M.op (M.op x x) (M.op x x)) X3
       grind)
    | (have r₁ := eq106 x x (M.op x x) (M.op x x)
       have r₂ := eq91 x x (k (M.op x x) (M.op x x)) X3
       grind)
    | exact resolve eq106 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq106
  have eq337 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq112 (σ X1) (σ X0)
       grind)
    | exact superpose eq112 eq15
    | exact resolve eq15 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq337 X0 X1
       have i₂ := eq112 X1 X0
       grind)
    | exact superpose eq112 eq337
    | exact resolve eq337 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq337
  have eq345 : False := by grind
  exact eq345

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq26 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq26 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq26 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq43 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq45 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq53 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq53
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq62
    | (have j0 := eq62 X0 X1
       grind)
    | exact resolve eq62 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq62
  have eq168 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq172 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       have j1 := eq65 X1 X0
       grind)
    | (have r₁ := eq168 X1 X0
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq168 X1 X1
       have r₂ := eq65 X1 X1
       grind)
    | exact resolve eq168 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq168
  have eq557 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq172 (σ X1) (σ X0)
       grind)
    | exact superpose eq172 eq15
    | exact resolve eq15 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq557 X0 X1
       have i₂ := eq172 X1 X0
       grind)
    | exact superpose eq172 eq557
    | exact resolve eq557 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq557
  have eq563 : False := by grind
  exact eq563

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq21 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X1 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq9 (M.op X0 X0) X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 : G, (k (τ X2) (k (τ X0) X1)) = (τ (k X2 (k X0 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq22
    | exact resolve eq22 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq46 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq31
    | exact resolve eq31 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq73 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq56 X1 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | (have j1 := eq56 X1 (τ X0)
       grind)
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq56
  have eq84 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X0 X0) X1 x
       have i₂ := eq9 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq67
    | exact resolve eq67 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq156 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | (have r₁ := eq34 x X1
       have r₂ := eq24 x x x
       grind)
    | (have r₁ := eq34 (M.op x x) X1
       have r₂ := eq24 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq34 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq163 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq156 (M.op X1 X1) X1
       have i₂ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq156
    | exact resolve eq156 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (k X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) = (σ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq156 X0 (τ X1)
       grind)
    | exact superpose eq156 eq17
    | exact resolve eq17 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq156
  have eq287 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (k (σ (τ X1)) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (τ X0)
       have i₂ := eq84 X0 (τ X0)
       grind)
    | (have i₁ := eq73 X0 (τ X0)
       have i₂ := eq84 (τ X0) X1
       grind)
    | exact superpose eq84 eq73
    | exact resolve eq73 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq84
  have eq313 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (k X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq287 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq287
    | (have j0 := eq287 X0 X1
       grind)
    | exact resolve eq287 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq348 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1
       have i₂ := eq313 X0 X1
       grind)
    | exact superpose eq313 eq11
    | (have j1 := eq313 X0 X1
       grind)
    | exact resolve eq11 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq169 (M.op X1 X1) X1
       have i₂ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq169
    | exact resolve eq169 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq513 : ∀ X0 X1 X2 : G, (τ (k X2 (k X1 (σ (M.op X0 X0))))) = (k (τ X2) (M.op (M.op X0 X0) (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36 X1 (M.op X0 X0) X2
       have i₂ := eq163 X0 (τ X1)
       grind)
    | exact superpose eq163 eq36
    | exact resolve eq36 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq517 : ∀ X0 X1 X2 : G, (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X0) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq422 X0 X1
       have i₂ := eq313 X0 X1
       grind)
    | exact superpose eq313 eq422
    | (have j1 := eq313 X2 X0
       grind)
    | exact resolve eq422 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq536 : ∀ X0 X1 X2 X3 : G, (σ (k (k (τ X2) (M.op (M.op X1 X1) (τ X0))) X3)) = (k (k X2 (k X0 (σ (M.op X1 X1)))) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X2 (M.op (M.op X1 X1) (τ X0)) X3
       have i₂ := eq422 X1 X0
       grind)
    | exact superpose eq422 eq21
    | exact resolve eq21 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq554 : ∀ X0 X1 X2 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X0) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq517 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq517
    | (have j0 := eq517 X0 X1 X2
       grind)
    | exact resolve eq517 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq629 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (σ X1)) (σ X2)
       have i₂ := eq135 X0 X1 X2
       grind)
    | exact superpose eq135 eq13
    | (have j0 := eq13 (k X0 (σ X1)) (σ X2)
       have j1 := eq135 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq135 X0 X1 X2
       grind)
    | exact resolve eq13 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (σ X2)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq629 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq631 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k (k (τ X0) X1) X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq630 X0 X1 X2
       have i₂ := eq21 X0 X1 X2
       grind)
    | exact superpose eq21 eq630
    | (have j0 := eq630 X0 X1 X2
       grind)
    | exact resolve eq630 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq630
  have eq2253 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq348 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq2307 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2253 X1 (M.op X0 X0)
       have i₂ := eq163 X0 (M.op X0 X0)
       grind)
    | exact superpose eq163 eq2253
    | (have j0 := eq2253 X1 (M.op X0 X0)
       grind)
    | exact resolve eq2253 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2253
  have eq2313 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2307 X0 X1
       grind)
    | (have r₁ := eq2307 x X1
       have r₂ := eq24 x x x
       grind)
    | (have r₁ := eq2307 (M.op x x) X1
       have r₂ := eq24 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq2307 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2307
  have eq2363 : ∀ X0 X2 X3 : G, (M.op (M.op (σ (M.op X0 X0)) X2) (M.op X3 X3)) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq9 X2 x X3
       have i₂ := eq2313 x X0
       grind)
    | exact superpose eq2313 eq9
    | exact resolve eq9 eq2313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2390 : ∀ X0 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq163 X0 x
       have i₂ := eq2313 X0 x
       grind)
    | exact superpose eq2313 eq163
    | exact resolve eq163 eq2313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq41218 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq631 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq41223 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq41218 X0 X1 X2
       have j1 := eq135 X0 X1 X2
       grind)
    | (have r₁ := eq41218 X0 X1 X2
       have r₂ := eq135 X0 X1 X2
       grind)
    | exact resolve eq41218 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq41218
  have eq376374 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq554 X0 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq376375 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq376374 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376374
  have eq376714 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq376375 X1
       have i₂ := eq2313 X0 (τ X1)
       grind)
    | exact superpose eq2313 eq376375
    | exact resolve eq376375 eq2313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2313 eq376375
  have eq401419 : ∀ X0 X1 X2 : G, (k (τ X2) (M.op (M.op X0 X0) (τ X1))) = (τ (k X2 (M.op (σ (M.op X0 X0)) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq513 X0 X1 X2
       have i₂ := eq2390 X0 X1
       grind)
    | exact superpose eq2390 eq513
    | exact resolve eq513 eq2390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq681255 : ∀ X0 X1 X2 : G, (M.op (σ (τ X2)) (k X0 (σ (τ X1)))) = (σ (τ (k (k (σ (τ X0)) X1) X2))) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41223 X0 (τ X1) (τ X2)
       have i₂ := eq46 (τ X0) X1 X2
       grind)
    | exact superpose eq46 eq41223
    | (have j0 := eq41223 X0 X1 (τ X2)
       grind)
    | exact resolve eq41223 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq41223
  have eq682293 : ∀ X0 X1 X2 : G, (k (k (σ (τ X0)) X1) X2) = (M.op (σ (τ X2)) (k X0 (σ (τ X1)))) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq681255 X0 X1 X2
       have i₂ := eq11 (k (k (σ (τ X0)) X1) X2)
       grind)
    | exact superpose eq11 eq681255
    | (have j0 := eq681255 X0 X1 X2
       grind)
    | exact resolve eq681255 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681255
  have eq682549 : ∀ X0 X1 X2 : G, (k (k (σ (τ X0)) X1) X2) = (M.op (σ (τ X2)) (k X0 X1)) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq682293 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq682293
    | (have j0 := eq682293 X0 X1 X2
       grind)
    | exact resolve eq682293 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682293
  have eq682648 : ∀ X0 X1 X2 : G, (k (k (σ (τ X0)) X1) X2) = (M.op X2 (k X0 X1)) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq682549 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq682549
    | (have j0 := eq682549 X0 X1 X2
       grind)
    | exact resolve eq682549 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682549
  have eq682701 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op X2 (k X0 X1)) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq682648 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq682648
    | (have j0 := eq682648 X0 X1 X2
       grind)
    | exact resolve eq682648 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682648
  have eq682723 : ∀ X0 X1 X2 : G, (M.op X2 X2) = X2 ∨ (k (k X0 X1) X2) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq682701 X0 X1 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq682701
    | (have j0 := eq682701 X0 X1 X2
       grind)
    | exact resolve eq682701 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682701
  have eq682729 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq682723 X0 X1 X2
       have j1 := eq12 (k X0 X1) X2
       grind)
    | (have r₁ := eq682723 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq682723 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682723
  have eq682772 : ∀ X0 X2 : G, (k (M.op X0 X0) X2) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq682729 x x X2
       have i₂ := eq376714 X0 x
       grind)
    | exact superpose eq376714 eq682729
    | exact resolve eq682729 eq376714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376714
  have eq738861 : ∀ X0 X1 X2 X3 : G, (σ (k (k (τ X2) (M.op (M.op X1 X1) (τ X0))) X3)) = (M.op (σ X3) (k X2 (k X0 (σ (M.op X1 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq536 X0 X1 X2 X3
       have i₂ := eq682729 X2 (k X0 (σ (M.op X1 X1))) (σ X3)
       grind)
    | exact superpose eq682729 eq536
    | exact resolve eq536 eq682729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq738862 : ∀ X0 X1 X2 X3 : G, (σ (k (k (τ X2) (M.op (M.op X1 X1) (τ X0))) X3)) = (M.op (σ X3) (k X2 (M.op (σ (M.op X1 X1)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq738861 X0 X1 X2 X3
       have i₂ := eq2390 X1 X0
       grind)
    | exact superpose eq2390 eq738861
    | exact resolve eq738861 eq2390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2390 eq738861
  have eq738863 : ∀ X0 X1 X2 X3 : G, (M.op (σ X3) (k X2 (M.op (σ (M.op X1 X1)) X0))) = (σ (M.op X3 (k (τ X2) (M.op (M.op X1 X1) (τ X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq738862 X0 X1 X2 X3
       have i₂ := eq682729 (τ X2) (M.op (M.op X1 X1) (τ X0)) X3
       grind)
    | exact superpose eq682729 eq738862
    | exact resolve eq738862 eq682729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682729 eq738862
  have eq738864 : ∀ X0 X1 X2 X3 : G, (M.op (σ X3) (k X2 (M.op (σ (M.op X1 X1)) X0))) = (σ (M.op X3 (τ (k X2 (M.op (σ (M.op X1 X1)) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq738863 X0 X1 X2 X3
       have i₂ := eq401419 X1 X0 X2
       grind)
    | exact superpose eq401419 eq738863
    | exact resolve eq738863 eq401419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401419 eq738863
  have eq949096 : ∀ X0 X1 X2 X3 : G, (M.op (σ X3) (M.op (M.op (σ (M.op X0 X0)) X1) (M.op X2 X2))) = (σ (M.op X3 (τ (M.op (M.op (σ (M.op X0 X0)) X1) (M.op X2 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq738864 X0 X1 (M.op X0 X0) X3
       have i₂ := eq682772 X0 (M.op (σ (M.op X1 X1)) X0)
       grind)
    | exact superpose eq682772 eq738864
    | exact resolve eq738864 eq682772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682772 eq738864
  have eq950250 : ∀ X1 X3 : G, (M.op (σ X3) X1) = (σ (M.op X3 (τ X1))) := by
    intro X1 X3
    first
    | (have i₁ := eq949096 x x X3 X3
       have i₂ := eq2363 x x X3
       grind)
    | exact superpose eq2363 eq949096
    | exact resolve eq949096 eq2363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2363 eq949096
  have eq951007 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq950250 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq950250
    | exact resolve eq950250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950250
  have eq955149 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq951007 y x
       grind)
    | exact superpose eq951007 eq16
    | (have r₁ := eq16
       have r₂ := eq951007 y x
       grind)
    | exact resolve eq16 eq951007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951007
  have eq956225 : False := by grind
  exact eq956225

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyy_pxy_Equation2132 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X3)) = X2 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X0 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq44 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq34
    | (have j0 := eq34 X0 X1
       grind)
    | exact resolve eq34 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq100 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2
       have i₂ := eq25 X0 (σ X2) X1
       grind)
    | exact superpose eq25 eq22
    | exact resolve eq22 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq25 (M.op X0 X0) X1 x
       grind)
    | (have i₁ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq25 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq44
    | (have j0 := eq44 (σ (k X0 X1)) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq44 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq131
    | (have j0 := eq131 X0 X1
       grind)
    | exact resolve eq131 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq231 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (M.op X0 X1) X2 x
       have i₂ := eq37 X0 X1 (M.op X0 X1) x
       grind)
    | exact superpose eq37 eq25
    | (have j1 := eq37 X0 X1 X2 x
       grind)
    | exact resolve eq25 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq37
  have eq256 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq50
    | (have j0 := eq50 X0 X1
       have j1 := eq44 X0 X1
       grind)
    | exact resolve eq50 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq710 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X2)) ∨ (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X1 X2
       have i₂ := eq107 X0 X1
       grind)
    | (have i₁ := eq50 X1 X2
       have i₂ := eq107 X1 X0
       grind)
    | exact superpose eq107 eq50
    | (have j0 := eq50 X1 X2
       grind)
    | exact resolve eq50 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq725 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq107 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq107 (σ X1) X0
       grind)
    | exact superpose eq107 eq22
    | exact resolve eq22 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1192 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (τ (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X2 X2)
       have i₂ := eq100 X0 X1 X2
       grind)
    | exact superpose eq100 eq10
    | exact resolve eq10 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq2403 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X1) ∨ (M.op X0 X0) = (k X2 X1) ∨ X1 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq152 X0 X1
       have i₂ := eq107 X0 X1
       grind)
    | (have i₁ := eq152 X0 X0
       have i₂ := eq107 X0 X1
       grind)
    | exact superpose eq107 eq152
    | (have j0 := eq152 (M.op X0 X0) (k X2 X1)
       grind)
    | (have r₁ := eq152 X0 X0
       have r₂ := eq107 X0 X0
       grind)
    | (have r₁ := eq152 X1 X1
       have r₂ := eq107 X1 X1
       grind)
    | exact resolve eq152 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq2450 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X1) ∨ (k X2 X1) = (M.op X2 X1) ∨ X1 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153 X2 X1
       have i₂ := eq107 X0 X1
       grind)
    | (have i₁ := eq153 X2 X1
       have i₂ := eq107 X1 X0
       grind)
    | exact superpose eq107 eq153
    | (have j0 := eq153 X2 X1
       grind)
    | (have r₁ := eq153 X0 X0
       have r₂ := eq107 X0 X0
       grind)
    | (have r₁ := eq153 X1 X1
       have r₂ := eq107 X1 X1
       grind)
    | exact resolve eq153 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq2479 : ∀ X1 X2 : G, (k X2 X1) = (M.op X2 X1) ∨ X1 = X2 := by
    intro X1 X2
    first
    | (have j0 := eq2450 x X1 X2
       have j1 := eq231 X2 X1 X2
       grind)
    | (have r₁ := eq2450 X2 X1 x
       have r₂ := eq231 x X1 X2
       grind)
    | (have r₁ := eq2450 X1 X2 X2
       have r₂ := eq231 X1 X1 X2
       grind)
    | (have r₁ := eq2450 x X1 X2
       have r₂ := eq231 (M.op x x) (M.op X2 X1) X2
       grind)
    | exact resolve eq2450 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq2450
  have eq6751 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq159 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq6753 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq6751 X0 X1
       have j1 := eq710 X0 X0 X1
       grind)
    | (have r₁ := eq6751 X1 X0
       have r₂ := eq710 X0 X1 X0
       grind)
    | exact resolve eq6751 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq6751
  have eq23978 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq256 x y
       grind)
    | exact superpose eq256 eq16
    | (have j1 := eq256 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq256 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq256 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq256 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq24411 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23978
  have eq128131 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (M.op X0 X0) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2403 X0 (σ y) (σ x)
       have i₂ := eq24411
       grind)
    | exact superpose eq24411 eq2403
    | (have j0 := eq2403 X0 (σ y) (σ x)
       grind)
    | exact resolve eq2403 eq24411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2403 eq24411
  have eq128168 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (M.op X0 X0) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq128131 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128131
  have eq128220 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq128168 X0
       grind)
    | (have r₁ := eq128168 X0
       have r₂ := eq725 X0 x
       grind)
    | exact resolve eq128168 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128168
  have eq128232 : ∀ X0 : G, (M.op X0 X0) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq128220 X0
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq128220
    | exact resolve eq128220 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128220
  have eq137096 : ∀ X0 : G, (M.op X0 X0) = (τ (σ (k x y))) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1192 x x X0
       have i₂ := eq128232 (M.op x x)
       grind)
    | exact superpose eq128232 eq1192
    | exact resolve eq1192 eq128232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192 eq128232
  have eq137491 : ∀ X0 : G, (k x y) = (M.op y y) ∨ (M.op X0 X0) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq137096 X0
       have i₂ := eq10 (k x y)
       grind)
    | exact superpose eq10 eq137096
    | exact resolve eq137096 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137096
  have eq151250 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (M.op X0 X0) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq137491 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151251 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq137491 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137491
  have eq151464 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq151251 x
       have r₂ := eq107 y x
       grind)
    | (have r₁ := eq151251 x
       have r₂ := eq107 x y
       grind)
    | exact resolve eq151251 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151251
  have eq151465 : ∀ X0 : G, (M.op X0 X0) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq151250 X0
       grind)
    | (have r₁ := eq151250 x
       have r₂ := eq107 y x
       grind)
    | (have r₁ := eq151250 X0
       have r₂ := eq107 X0 y
       grind)
    | exact resolve eq151250 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq151250
  have eq173309 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2479 y x
       have i₂ := eq151464
       grind)
    | exact superpose eq151464 eq2479
    | (have j0 := eq2479 (M.op x y) (M.op y y)
       grind)
    | exact resolve eq2479 eq151464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479 eq151464
  have eq173314 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq173309
  have eq198194 : ∀ X0 : G, (M.op X0 X0) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq725 X0 x
       have i₂ := eq151465 x
       grind)
    | exact superpose eq151465 eq725
    | exact resolve eq725 eq151465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151465
  have eq217364 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq725 X0 y
       have i₂ := eq173314
       grind)
    | exact superpose eq173314 eq725
    | exact resolve eq725 eq173314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173314
  have eq280800 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq6753 x y
       have i₂ := eq198194 X0
       grind)
    | exact superpose eq198194 eq6753
    | (have j0 := eq6753 x y
       grind)
    | exact resolve eq6753 eq198194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6753 eq198194
  have eq280919 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq280800 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280800
  have eq1124926 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq280919 X0
       grind)
    | exact superpose eq280919 eq16
    | exact resolve eq16 eq280919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280919
  have eq1125496 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1124926 x
       have r₂ := eq217364 x
       grind)
    | exact resolve eq1124926 eq217364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217364 eq1124926
  have eq1185000 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1125496
       grind)
    | exact superpose eq1125496 eq10
    | exact resolve eq10 eq1125496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125496
  have eq1185389 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1185000
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1185000
    | exact resolve eq1185000 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185000
  have eq1185390 : x = y := by grind
  clear eq1185389
  have eq1269282 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1185390
       grind)
    | exact superpose eq1185390 eq16
    | exact resolve eq16 eq1185390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185390
  have eq1269283 : False := by grind
  exact eq1269283

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation2132 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (k (τ (σ X0)) X0) = (M.op (τ (σ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq12 (τ (σ X0)) X0
       grind)
    | (have r₁ := eq12 (τ (σ X0)) X0
       have r₂ := eq10 X0
       grind)
    | (have r₁ := eq12 X0 (τ (σ X0))
       have r₂ := eq10 X0
       grind)
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq17 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17
    | exact resolve eq17 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq15
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq36
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq36
  have eq101 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq108 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq109 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq110 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X0 X1
       have i₂ := eq37 X1
       grind)
    | exact superpose eq37 eq106
    | (have j0 := eq106 X0 X1
       grind)
    | exact resolve eq106 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq277 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq109 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq109
    | (have j0 := eq109 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq109 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq109 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq307 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq304 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq304 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq304 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq304 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq304 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq311 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq277 X0 X1
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq277
    | (have j0 := eq277 X0 X1
       grind)
    | exact resolve eq277 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq819 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq831 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq819 X0 X1
       have j1 := eq311 X1 X0
       grind)
    | (have r₁ := eq819 X1 X0
       have r₂ := eq311 X0 X1
       grind)
    | (have r₁ := eq819 X0 X1
       have r₂ := eq311 (k X1 X0) (M.op X1 X1)
       grind)
    | (have r₁ := eq819 X0 X1
       have r₂ := eq311 (M.op X1 X1) (k X1 X0)
       grind)
    | exact resolve eq819 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311 eq819
  have eq1432 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq307 X1 (τ X0)
       grind)
    | exact superpose eq307 eq28
    | (have j1 := eq307 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq28 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq307
  have eq5475 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq831 x y
       grind)
    | exact superpose eq831 eq16
    | (have j1 := eq831 x y
       grind)
    | exact resolve eq16 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq62702 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1432 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1432
    | exact resolve eq1432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq62845 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62702 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq62702
    | (have j0 := eq62702 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq62702 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62702
  have eq64768 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5475
       have i₂ := eq62845 x y
       grind)
    | exact superpose eq62845 eq5475
    | (have j1 := eq62845 (σ x) (σ y)
       grind)
    | (have r₁ := eq5475
       have r₂ := eq62845 x y
       grind)
    | (have r₁ := eq5475
       have r₂ := eq62845 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5475
       have r₂ := eq62845 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5475 eq62845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5475 eq62845
  have eq64769 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq64768
  have eq64778 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq64769
       grind)
    | exact superpose eq64769 eq10
    | exact resolve eq10 eq64769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64769
  have eq64864 : x = y ∨ x = y := by
    first
    | (have i₁ := eq64778
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq64778
    | exact resolve eq64778 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64778
  have eq64865 : x = y := by grind
  clear eq64864
  have eq65140 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64865
       grind)
    | exact superpose eq64865 eq16
    | exact resolve eq16 eq64865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64865
  have eq65141 : False := by grind
  exact eq65141

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation2132 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq25 (M.op X0 X0) X1 x
       grind)
    | (have i₁ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq25 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq125 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq117 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq117 X0 X1
       grind)
    | exact resolve eq13 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq125 (σ X0) (σ X1)
       grind)
    | exact superpose eq125 eq15
    | (have j1 := eq125 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 X1
       have i₂ := eq125 X0 X1
       grind)
    | exact superpose eq125 eq140
    | (have j0 := eq140 X0 X1
       have j1 := eq125 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq140 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq140
  have eq239 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq117 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq117 (σ X1) X0
       grind)
    | exact superpose eq117 eq22
    | exact resolve eq22 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq117
  have eq1524 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq142 x y
       grind)
    | exact superpose eq142 eq16
    | (have j1 := eq142 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq142 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq142 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq142 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq1528 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1524
  have eq3104 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1528
       grind)
    | exact superpose eq1528 eq10
    | exact resolve eq10 eq1528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528
  have eq3129 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3104
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3104
    | exact resolve eq3104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3104
  have eq3130 : x = y := by grind
  clear eq3129
  have eq3575 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3130
       grind)
    | exact superpose eq3130 eq16
    | exact resolve eq16 eq3130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3130
  have eq3576 : False := by grind
  exact eq3576

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation2132 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq75 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq25 (M.op X0 X0) X1 x
       grind)
    | (have i₁ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq25 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq29
    | (have j0 := eq29 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq75 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq75 (σ X1) X0
       grind)
    | exact superpose eq75 eq22
    | exact resolve eq22 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq75
  have eq1553 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq82 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq82 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq82 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1564 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1553
  have eq1758 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1564
       grind)
    | exact superpose eq1564 eq16
    | exact resolve eq16 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1759 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq1564
       grind)
    | exact superpose eq1564 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1564
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1564
       grind)
    | exact resolve eq13 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq1760 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1759
  have eq1761 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1760
  have eq1763 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1761
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1761
    | exact resolve eq1761 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1761
  have eq7232 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1763
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1763
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq1763 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7235 : (k y x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq1763
       grind)
    | exact superpose eq1763 eq10
    | exact resolve eq10 eq1763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1763
  have eq7254 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq7232
  have eq7259 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq7235
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7235
    | exact resolve eq7235 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7235
  have eq7260 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq7254
       have r₂ := eq1758
       grind)
    | exact resolve eq7254 eq1758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758 eq7254
  have eq7261 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x (k y x)
       grind)
    | (have r₁ := eq7259
       have r₂ := eq13 y x
       grind)
    | exact resolve eq7259 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7259
  have eq19809 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq29 x y
       have i₂ := eq7261
       grind)
    | exact superpose eq7261 eq29
    | (have j0 := eq29 x y
       grind)
    | exact resolve eq29 eq7261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq7261
  have eq19812 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19809
  have eq23261 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq19812
       grind)
    | exact superpose eq19812 eq16
    | exact resolve eq16 eq19812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19812
  have eq36631 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq23261
       have i₂ := eq7260
       grind)
    | exact superpose eq7260 eq23261
    | exact resolve eq23261 eq7260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7260 eq23261
  have eq36632 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq36631
  have eq36633 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq36632
  have eq53641 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq36633
       grind)
    | exact superpose eq36633 eq10
    | exact resolve eq10 eq36633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36633
  have eq53664 : x = y ∨ x = y := by
    first
    | (have i₁ := eq53641
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq53641
    | exact resolve eq53641 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53641
  have eq53665 : x = y := by grind
  clear eq53664
  have eq56011 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53665
       grind)
    | exact superpose eq53665 eq16
    | exact resolve eq16 eq53665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53665
  have eq56012 : False := by grind
  exact eq56012

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pyx_pxx_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
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
  clear eq25
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq23 eq37
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq341 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq52 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 (M.op x (M.op (M.op X0 X0) (M.op X1 X1)))
       have i₂ := eq52 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq52 eq65
    | exact resolve eq65 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq65
  have eq33712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33713 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq33712
    | exact resolve eq33712 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33712
  have eq33724 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq33713
       have r₂ := eq28
       grind)
    | exact resolve eq33713 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33713
  have eq33726 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq33724
       have i₂ := eq341 X0 sF3
       grind)
    | (have i₁ := eq33724
       have i₂ := eq341 sF3 x
       grind)
    | exact superpose eq341 eq33724
    | exact resolve eq33724 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33724
  have eq33970 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq33726 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33726
  have eq33971 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq33970
  have eq33990 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq33971
  have eq34110 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq33990
    | exact resolve eq33990 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33990
  have eq35526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq34110 eq96
    | exact resolve eq96 eq34110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq34110
  have eq35536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq35526
  have eq35538 : y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq35536
       have r₂ := eq28
       grind)
    | exact resolve eq35536 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35536
  have eq35540 : ∀ X0 : G, y = (M.op x x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq35538
       have i₂ := eq341 X0 y
       grind)
    | (have i₁ := eq35538
       have i₂ := eq341 y X0
       grind)
    | exact superpose eq341 eq35538
    | exact resolve eq35538 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35538
  have eq35789 : y ≠ y ∨ y = (M.op x x) := by
    first
    | (have j0 := eq35540 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35540
  have eq35790 : y = (M.op x x) := by grind
  clear eq35789
  have eq35803 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq35790
       have i₂ := eq341 X0 x
       grind)
    | (have i₁ := eq35790
       have i₂ := eq341 x X0
       grind)
    | exact superpose eq341 eq35790
    | exact resolve eq35790 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq35809 : (M.op x y) = (k y x) := by grind
  have eq35863 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq550 X0 x
       have i₂ := eq35790
       grind)
    | exact superpose eq35790 eq550
    | exact resolve eq550 eq35790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq35790
  have eq35932 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq35809
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq35809
    | exact resolve eq35809 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq35809
  have eq36545 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq35932
       grind)
    | exact superpose eq35932 eq72
    | exact resolve eq72 eq35932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq35932
  have eq36567 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq36545
    | exact resolve eq36545 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq36545
  have eq37401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq36567 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq36567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq37401
    | exact resolve eq37401 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37401
  have eq37415 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq37402
       have r₂ := eq28
       grind)
    | exact resolve eq37402 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37402
  have eq37419 : y = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq37415
       have i₂ := eq35803 sF3
       grind)
    | exact superpose eq35803 eq37415
    | exact resolve eq37415 eq35803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37415
  have eq37424 : y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq37419
       have i₂ := eq35803 sF2
       grind)
    | exact superpose eq35803 eq37419
    | exact resolve eq37419 eq35803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35803 eq37419
  have eq37425 : y = (σ y) := by grind
  clear eq37424
  have eq37430 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq37425 eq27
    | exact resolve eq27 eq37425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq37520 : (σ (M.op x y)) = (k y (σ x)) := by
    first
    | exact superpose eq37425 eq36567
    | exact resolve eq36567 eq37425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36567 eq37425
  have eq39006 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq37520
       have i₂ := eq35863 sF2
       grind)
    | exact superpose eq35863 eq37520
    | exact resolve eq37520 eq35863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35863 eq37520
  have eq39007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37430 eq39006
    | exact resolve eq39006 eq37430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37430 eq39006
  have eq39086 : False := by grind
  exact eq39086
