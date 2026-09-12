import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pxy_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq29 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq29 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq48 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X1 (k X1 X1)
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq49 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq49 X1 (k X1 X1)
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq49 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq55
    | (have j0 := eq55 X0 X1
       grind)
    | exact resolve eq55 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq55
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq60 X0 X1
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq61 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq61
  have eq218 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq224 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq218 X0 X1
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq218 X0 X1
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq218 X1 X1
       have r₂ := eq63 X1 X1
       grind)
    | exact resolve eq218 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq218
  have eq585 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq224 (σ X0) (σ X1)
       grind)
    | exact superpose eq224 eq15
    | exact resolve eq15 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq585 X0 X1
       have i₂ := eq224 X0 X1
       grind)
    | exact superpose eq224 eq585
    | exact resolve eq585 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq585
  have eq595 : False := by grind
  exact eq595

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_y_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  clear eq22
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
  clear eq35
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X1 X2)) ∨ (k (M.op X0 (M.op X1 X2)) X1) = (M.op (M.op X0 (M.op X1 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 (M.op X1 X2)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X0 (M.op X1 X2)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 X2) (M.op X1 X2)) X1
       have r₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq36
  have eq92 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq98 x y
       grind)
    | exact superpose eq98 eq44
    | (have j1 := eq98 x y
       grind)
    | exact resolve eq44 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq123 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq124 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq123
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq123
    | exact resolve eq123 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq124 eq98
    | (have j0 := eq98 (σ x) (σ y)
       grind)
    | exact resolve eq98 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq128
       have r₂ := eq27
       grind)
    | exact resolve eq128 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq133 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq131
    | exact resolve eq131 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq224 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq133 eq52
    | exact resolve eq52 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq250 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq236
    | (have j0 := eq236 (σ x)
       grind)
    | exact resolve eq236 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133 eq250
    | exact resolve eq250 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq267 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq262
  have eq268 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq267
    | exact resolve eq267 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq275 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (σ x) (M.op X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq236 X0
       grind)
    | exact superpose eq236 eq55
    | exact resolve eq55 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq288 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq295 : ∀ X1 : G, (M.op X1 X1) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq275 X1 X1
       have i₂ := eq14 sF2 X1 sF3
       grind)
    | exact superpose eq14 eq275
    | exact resolve eq275 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq305 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq295 X1
       have i₂ := eq295 sF2
       grind)
    | exact superpose eq295 eq295
    | exact resolve eq295 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq268
       have i₂ := eq295 sF2
       grind)
    | exact superpose eq295 eq268
    | exact resolve eq268 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq295
  have eq324 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq319 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq328 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq305 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq332 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X0 (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq324 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq324
    | exact resolve eq324 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (M.op (σ x) (σ y)) = (k X0 X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq324 X0
       grind)
    | exact superpose eq324 eq13
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       have r₂ := eq324 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq324 X0
       grind)
    | exact resolve eq13 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq817 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X0 X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq332 sF0
       have i₂ := eq328 sF0 x
       grind)
    | (have i₁ := eq332 sF0
       have i₂ := eq328 X0 sF0
       grind)
    | exact superpose eq328 eq332
    | exact resolve eq332 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328 eq332
  have eq827 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq817 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq6578 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq346 (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq6580 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133 eq6578
    | exact resolve eq6578 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq6578
  have eq6589 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6580
  have eq6592 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6589 eq92
    | exact resolve eq92 eq6589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq6589
  have eq6599 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq6592
    | exact resolve eq6592 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6592
  have eq6602 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq98 y y
       have i₂ := eq6599
       grind)
    | exact superpose eq6599 eq98
    | (have j0 := eq98 y y
       grind)
    | exact resolve eq98 eq6599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6599
  have eq6603 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq6602
  have eq6619 : y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq324 y
       have i₂ := eq6603
       grind)
    | exact superpose eq6603 eq324
    | exact resolve eq324 eq6603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq6626 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq827 y
       have i₂ := eq6603
       grind)
    | exact superpose eq6603 eq827
    | exact resolve eq827 eq6603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq6603
  have eq6649 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6626
  have eq6655 : y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6619
  have eq6663 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6649
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6649
    | exact resolve eq6649 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6649
  have eq6798 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6663 eq6655
    | exact resolve eq6655 eq6663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6655 eq6663
  have eq6799 : y = (M.op x y) := by grind
  clear eq6798
  have eq6825 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq6799 eq20
    | exact resolve eq20 eq6799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq6843 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq6825
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6825
    | exact resolve eq6825 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6825
  have eq6845 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq6843 eq26
    | exact resolve eq26 eq6843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq6973 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op x (M.op X1 y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq6799 eq224
    | exact resolve eq224 eq6799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq7107 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq51 eq6973
    | exact resolve eq6973 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq6973
  have eq7182 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7107 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7107
    | (have j0 := eq7107 X0
       grind)
    | exact resolve eq7107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7107
  have eq7214 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq6799 eq7182
    | exact resolve eq7182 eq6799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7182
  have eq7219 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7214 X0
       have i₂ := eq288 X0 X0
       grind)
    | exact superpose eq288 eq7214
    | exact resolve eq7214 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq7214
  have eq7221 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7219 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7219
    | (have j0 := eq7219 X0
       grind)
    | exact resolve eq7219 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7219
  have eq7223 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq6799 eq7221
    | exact resolve eq7221 eq6799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6799 eq7221
  have eq7324 : ∀ X1 : G, y = (M.op X1 y) := by
    intro X1
    first
    | (have i₁ := eq54 x (M.op x x) x
       have i₂ := eq7223 (M.op x x)
       grind)
    | exact superpose eq7223 eq54
    | exact resolve eq54 eq7223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq7330 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq69 (M.op x x) x x
       have i₂ := eq7223 (M.op x x)
       grind)
    | exact superpose eq7223 eq69
    | exact resolve eq69 eq7223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq7383 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq7330 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7330
  have eq7534 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq7383 y
       grind)
    | exact superpose eq7383 eq77
    | exact resolve eq77 eq7383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq7383
  have eq7537 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq7534
       have i₂ := eq7223 y
       grind)
    | exact superpose eq7223 eq7534
    | exact resolve eq7534 eq7223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7534
  have eq7541 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6843 eq7537
    | exact resolve eq7537 eq6843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7537
  have eq7544 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq7541
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7541
    | exact resolve eq7541 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7541
  have eq7546 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6843 eq7544
    | exact resolve eq7544 eq6843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6843 eq7544
  have eq7551 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7546 eq98
    | (have j0 := eq98 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq98 eq7546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq7546
  have eq7552 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq7551
  have eq7554 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq7552
       have i₂ := eq7223 sF1
       grind)
    | exact superpose eq7223 eq7552
    | exact resolve eq7552 eq7223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7223 eq7552
  have eq7568 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq7554 eq6845
    | exact resolve eq6845 eq7554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6845
  have eq7571 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7568
       have i₂ := eq7324 sF2
       grind)
    | exact superpose eq7324 eq7568
    | exact resolve eq7568 eq7324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7324 eq7568
  have eq7607 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq7571 eq27
    | exact resolve eq27 eq7571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq7571
  have eq7643 : False := by grind
  exact eq7643

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 X1
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X2 X0
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
  have eq31 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = X0 ∨ (k X3 X0) = (M.op X3 X0) ∨ (M.op X0 X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X3 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X3 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq30 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq40 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = X0 ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq31 X0 X1 X2 X3
       have j1 := eq12 X3 X0
       grind)
    | (have r₁ := eq31 X1 X1 X2 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq41 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq36 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq36 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq36 X1 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq298 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 X0 X1 x X1
       have i₂ := eq40 X0 X1 (M.op X0 x) X3
       grind)
    | exact superpose eq40 eq20
    | (have j1 := eq40 X0 X1 x X3
       grind)
    | exact resolve eq20 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq40
  have eq364 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq41 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq369 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq364 X0 X1
       have j1 := eq298 X1 X1 X0
       grind)
    | (have r₁ := eq364 X0 X0
       have r₂ := eq298 X0 X0 x
       grind)
    | (have r₁ := eq364 X1 X0
       have r₂ := eq298 X0 X1 x
       grind)
    | exact resolve eq364 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq364
  have eq374 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq369 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq369 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq369 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq544 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq374 (σ X0) (σ X1)
       grind)
    | exact superpose eq374 eq15
    | exact resolve eq15 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq544 X0 X1
       have i₂ := eq374 X0 X1
       grind)
    | exact superpose eq374 eq544
    | exact resolve eq544 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374 eq544
  have eq552 : False := by grind
  exact eq552

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq29 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq29 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq48 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq49 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq49 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq55
    | (have j0 := eq55 X0 X1
       grind)
    | exact resolve eq55 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq55
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq60 X0 X1
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq61 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq61
  have eq216 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq222 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq216 X0 X1
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq216 X0 X1
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq216 X1 X1
       have r₂ := eq63 X1 X1
       grind)
    | exact resolve eq216 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq216
  have eq583 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq222 (σ X0) (σ X1)
       grind)
    | exact superpose eq222 eq15
    | exact resolve eq15 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq583 X0 X1
       have i₂ := eq222 X0 X1
       grind)
    | exact superpose eq222 eq583
    | exact resolve eq583 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq583
  have eq593 : False := by grind
  exact eq593

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 X1
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X2 X0
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
  have eq31 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = X0 ∨ (k X3 X0) = (M.op X3 X0) ∨ (M.op X0 X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X3 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X3 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq30 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq40 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = X0 ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq31 X0 X1 X2 X3
       have j1 := eq12 X3 X0
       grind)
    | (have r₁ := eq31 X1 X1 X2 X3
       have r₂ := eq12 (M.op X1 (M.op X1 X2)) X1
       grind)
    | (have r₁ := eq31 X1 X1 X2 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq41 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq36 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq36 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq36 X1 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq295 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 X0 X1 x X1
       have i₂ := eq40 X0 X1 (M.op X0 x) X3
       grind)
    | exact superpose eq40 eq20
    | (have j1 := eq40 X0 X1 x X3
       grind)
    | exact resolve eq20 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq40
  have eq361 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq41 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq366 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq361 X0 X1
       have j1 := eq295 X1 X1 X0
       grind)
    | (have r₁ := eq361 X0 X0
       have r₂ := eq295 X0 X0 x
       grind)
    | (have r₁ := eq361 X1 X0
       have r₂ := eq295 X0 X1 x
       grind)
    | exact resolve eq361 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq361
  have eq369 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq366 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq366 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq366 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq539 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq369 (σ X0) (σ X1)
       grind)
    | exact superpose eq369 eq15
    | exact resolve eq15 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq539 X0 X1
       have i₂ := eq369 X0 X1
       grind)
    | exact superpose eq369 eq539
    | exact resolve eq539 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq539
  have eq547 : False := by grind
  exact eq547

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pxy_pyx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X2))) X1) = (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X1) := by
    intro X0 X1 X2
    grind
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq233 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x X0
       have i₂ := eq56 x X1
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq67 x X1 (M.op X0 (M.op X1 (M.op X0 x)))
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq67
    | exact resolve eq67 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq67
  have eq977 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq951 X0 X1
       have i₂ := eq241 X0 X0
       grind)
    | exact superpose eq241 eq951
    | exact resolve eq951 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq1371 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X0
       have i₂ := eq56 X0 (σ X0)
       grind)
    | exact superpose eq56 eq77
    | exact resolve eq77 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1387 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq56
    | (have j1 := eq77 X0 X0
       grind)
    | exact resolve eq56 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1405 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1406 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1405 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq1416 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1387 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq1432 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1371 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq1438 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1416 X0 X1
       have i₂ := eq241 X1 X1
       grind)
    | exact superpose eq241 eq1416
    | (have j0 := eq1416 X0 X1
       grind)
    | exact resolve eq1416 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416
  have eq1441 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1432 X0 X1
       have i₂ := eq241 X0 X0
       grind)
    | exact superpose eq241 eq1432
    | (have j0 := eq1432 X0 X1
       grind)
    | exact resolve eq1432 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq1470 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1441 X0 X1
       have i₂ := eq241 X0 X0
       grind)
    | exact superpose eq241 eq1441
    | (have j0 := eq1441 X0 X1
       grind)
    | exact resolve eq1441 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq1441
  have eq1471 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq296 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq296
    | exact resolve eq296 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq5615 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1470 X0 (τ X1)
       grind)
    | exact superpose eq1470 eq35
    | (have j1 := eq1470 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq5645 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5615 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5615
    | (have j0 := eq5615 X0 X1
       grind)
    | exact resolve eq5615 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5615
  have eq5705 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5645 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5645
    | (have j0 := eq5645 X0 X1
       grind)
    | exact resolve eq5645 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5645
  have eq8348 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5705 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5705
  have eq8459 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8348 X1 (τ X0)
       have i₂ := eq1471 X0 X0
       grind)
    | exact superpose eq1471 eq8348
    | (have j0 := eq8348 X1 (τ X0)
       grind)
    | exact resolve eq8348 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471
  have eq10327 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1406 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq1406
    | (have j0 := eq1406 (τ X0)
       grind)
    | exact resolve eq1406 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10335 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10327 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10327
    | (have j0 := eq10327 X0
       grind)
    | exact resolve eq10327 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10327
  have eq10344 : ∀ X0 : G, (σ (τ X0)) = (M.op x (M.op (σ (τ X0)) (M.op x y))) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq10335 X0
       have i₂ := eq52 (σ (τ X0))
       grind)
    | exact superpose eq52 eq10335
    | (have j0 := eq10335 X0
       grind)
    | exact resolve eq10335 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10335
  have eq10349 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op x (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10344 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10344
    | (have j0 := eq10344 X0
       grind)
    | exact resolve eq10344 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10344
  have eq10481 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1438 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1438
    | (have j0 := eq1438 (τ X0) X1
       grind)
    | exact resolve eq1438 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10562 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq1438 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1438
    | (have j0 := eq1438 x X0
       grind)
    | exact resolve eq1438 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438
  have eq10668 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10562 X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10562
    | exact resolve eq10562 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10562
  have eq10748 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (σ (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10481 X0 X1
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq10481
    | (have j0 := eq10481 X0 X1
       grind)
    | exact resolve eq10481 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq10481
  have eq10751 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10748 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10748
    | (have j0 := eq10748 X0 X1
       grind)
    | exact resolve eq10748 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10748
  have eq11364 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op x (M.op (σ x) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq10668 eq10349
    | (have j0 := eq10349 (σ x)
       grind)
    | exact resolve eq10349 eq10668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10349 eq10668
  have eq11375 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq52 eq11364
    | (have j0 := eq11364 X0
       grind)
    | exact resolve eq11364 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq11364
  have eq11376 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq11375 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11375
  have eq11642 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op X0 X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq10751 x X0
       grind)
    | exact superpose eq10751 eq44
    | (have j1 := eq10751 x x
       grind)
    | exact resolve eq44 eq10751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq10751
  have eq20503 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq78 X0
       grind)
    | (have r₁ := eq78 X0
       have r₂ := eq11376 (σ x)
       grind)
    | (have r₁ := eq78 X0
       have r₂ := eq11376 (σ X0)
       grind)
    | exact resolve eq78 eq11376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq20594 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20503 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20503
    | (have j0 := eq20503 y
       grind)
    | exact resolve eq20503 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20503
  have eq20613 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20594
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq20594
    | exact resolve eq20594 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20594
  have eq20633 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq20613
    | exact resolve eq20613 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20613
  have eq43681 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq93 eq20633
    | exact resolve eq20633 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq20633
  have eq43692 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq43681
       have r₂ := eq28
       grind)
    | exact resolve eq43681 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43681
  have eq43711 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq43692
       have i₂ := eq233 sF2 x
       grind)
    | (have i₁ := eq43692
       have i₂ := eq233 X0 sF2
       grind)
    | exact superpose eq233 eq43692
    | exact resolve eq43692 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43692
  have eq43835 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq11642 y
       have i₂ := eq43711 X0
       grind)
    | exact superpose eq43711 eq11642
    | (have j1 := eq43711 X0
       grind)
    | exact resolve eq11642 eq43711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11642 eq43711
  have eq43860 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq43835 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43835
  have eq43873 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq43860 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq43860
    | (have j0 := eq43860 X0
       grind)
    | exact resolve eq43860 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43860
  have eq43883 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq43873 X0
       have j1 := eq8348 x x
       grind)
    | (have r₁ := eq43873 X0
       have r₂ := eq8348 X0 (σ x)
       grind)
    | exact resolve eq43873 eq8348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8348 eq43873
  have eq43887 : ∀ X0 : G, (k x x) = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    grind
  have eq44905 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1406 x
       have i₂ := eq43887 X0
       grind)
    | exact superpose eq43887 eq1406
    | (have j0 := eq1406 x
       have j1 := eq43887 (σ x)
       grind)
    | exact resolve eq1406 eq43887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406 eq43887
  have eq44944 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44905 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44905
    | (have j0 := eq44905 (σ x)
       grind)
    | exact resolve eq44905 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44905
  have eq44962 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44944 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44944
    | (have j0 := eq44944 (σ x)
       grind)
    | exact resolve eq44944 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44944
  have eq44971 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq44962 (σ x)
       grind)
    | (have r₁ := eq44962 x
       have r₂ := eq11376 (σ x)
       grind)
    | (have r₁ := eq44962 x
       have r₂ := eq11376 x
       grind)
    | exact resolve eq44962 eq11376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44962
  have eq45559 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44971
       have i₂ := eq43883 X0
       grind)
    | exact superpose eq43883 eq44971
    | (have j1 := eq43883 (σ x)
       grind)
    | exact resolve eq44971 eq43883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43883 eq44971
  have eq45576 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq45559 (σ x)
       grind)
    | (have r₁ := eq45559 x
       have r₂ := eq11376 (σ x)
       grind)
    | (have r₁ := eq45559 x
       have r₂ := eq11376 x
       grind)
    | exact resolve eq45559 eq11376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11376 eq45559
  have eq45578 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq45576
       have r₂ := eq23
       grind)
    | exact resolve eq45576 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq45576
  have eq45579 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq45578
       have i₂ := eq233 sF2 x
       grind)
    | (have i₁ := eq45578
       have i₂ := eq233 X0 sF2
       grind)
    | exact superpose eq233 eq45578
    | exact resolve eq45578 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq45582 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by grind
  have eq45599 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq45578 eq977
    | exact resolve eq977 eq45578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq45656 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq45578 eq45582
    | exact resolve eq45582 eq45578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45578 eq45582
  have eq46162 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | exact superpose eq45656 eq8459
    | (have j0 := eq8459 (σ x) X0
       grind)
    | exact resolve eq8459 eq45656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8459 eq45656
  have eq46181 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | (have j0 := eq46162 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46162
  have eq46201 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq29 eq46181
    | exact resolve eq46181 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq46181
  have eq46221 : x = (σ x) := by
    first
    | (have i₁ := eq46201 x
       have i₂ := eq45579 x
       grind)
    | exact superpose eq45579 eq46201
    | exact resolve eq46201 eq45579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45579 eq46201
  have eq46225 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq46221 eq27
    | exact resolve eq27 eq46221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq48828 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq46221 eq45599
    | exact resolve eq45599 eq46221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45599
  have eq48904 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq48828 y
       grind)
    | exact superpose eq48828 eq45
    | exact resolve eq45 eq48828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq48940 : (σ (M.op x y)) = (k x (σ y)) := by
    first
    | exact superpose eq46221 eq48904
    | exact resolve eq48904 eq46221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46221 eq48904
  have eq49017 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq48940
       have i₂ := eq48828 sF3
       grind)
    | exact superpose eq48828 eq48940
    | exact resolve eq48940 eq48828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48828 eq48940
  have eq49089 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46225 eq49017
    | exact resolve eq49017 eq46225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46225 eq49017
  have eq49137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq49089
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq49089
    | exact resolve eq49089 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq49089
  have eq49170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq49137
    | exact resolve eq49137 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq49137
  have eq49190 : False := by grind
  exact eq49190

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  clear eq24 eq48
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
  have eq176 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op X1 x)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq180 x X0
       have i₂ := eq180 x X1
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1
       have i₂ := eq180 X0 X1
       grind)
    | exact superpose eq180 eq176
    | exact resolve eq176 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X2
       have i₂ := eq180 X0 X2
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 X1
       have i₂ := eq180 X1 X0
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq218 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq213 X0 X1 X2
       have i₂ := eq179 X0 X0 X1
       grind)
    | exact superpose eq179 eq213
    | exact resolve eq213 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq213
  have eq221 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq210 X0 X1
       have i₂ := eq215 X0 X0
       grind)
    | exact superpose eq215 eq210
    | exact resolve eq210 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq283 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op x y))) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0
       have i₂ := eq215 X1 X0
       grind)
    | (have i₁ := eq176 (M.op X0 X0)
       have i₂ := eq215 X0 (M.op X0 X0)
       grind)
    | exact superpose eq215 eq176
    | exact resolve eq176 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq215
  have eq573 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq630 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq657 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq573 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq573
    | exact resolve eq573 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq1810 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1815 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1944 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1973 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1944 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1944 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq1944 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq1944 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq1944 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944
  have eq2116 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq1973 X0
       grind)
    | exact superpose eq1973 eq183
    | exact resolve eq183 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq2118 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq208 X1 X0
       have i₂ := eq1973 X0
       grind)
    | exact superpose eq1973 eq208
    | exact resolve eq208 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq2122 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq218 X2 X0 X1
       have i₂ := eq1973 X0
       grind)
    | exact superpose eq1973 eq218
    | exact resolve eq218 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq2124 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op x y))) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq221 X0 X1
       have i₂ := eq1973 X0
       grind)
    | exact superpose eq1973 eq221
    | exact resolve eq221 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq2168 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op X1 (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2122 X0 X1 X2
       have i₂ := eq1973 X2
       grind)
    | exact superpose eq1973 eq2122
    | exact resolve eq2122 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122
  have eq2235 : ∀ X0 X1 : G, (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1973 X0
       have i₂ := eq2118 X1 X0
       grind)
    | exact superpose eq2118 eq1973
    | exact resolve eq1973 eq2118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2259 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq2118 (σ X1) X0
       grind)
    | exact superpose eq2118 eq10
    | exact resolve eq10 eq2118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2260 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq630 X1 (σ X1)
       have i₂ := eq2118 (σ X1) X0
       grind)
    | exact superpose eq2118 eq630
    | exact resolve eq630 eq2118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq2261 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq657 X1 X1
       have i₂ := eq2118 (τ X1) X0
       grind)
    | exact superpose eq2118 eq657
    | exact resolve eq657 eq2118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118
  have eq2266 : ∀ X0 X1 : G, (k X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2260 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq2260
    | exact resolve eq2260 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260
  have eq2288 : ∀ X0 X1 : G, (k X1 X1) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2266 X0 X1
       have i₂ := eq1973 X0
       grind)
    | exact superpose eq1973 eq2266
    | exact resolve eq2266 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266
  have eq2603 : ∀ X0 X2 : G, (τ (k X0 X0)) = (σ (k X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq2259 x X2
       have i₂ := eq2261 x X0
       grind)
    | exact superpose eq2261 eq2259
    | exact resolve eq2259 eq2261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259 eq2261
  have eq4265 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1810
       grind)
    | exact superpose eq1810 eq41
    | exact resolve eq41 eq1810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4266 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq4265
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4265
    | exact resolve eq4265 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4265
  have eq4268 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq4266
    | exact resolve eq4266 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4266
  have eq4276 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq4268 eq1815
    | exact resolve eq1815 eq4268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4283 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq4276
       have r₂ := eq27
       grind)
    | exact resolve eq4276 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4276
  have eq4288 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq4283 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq4283
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq4283
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq4283
       grind)
    | exact resolve eq12 eq4283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4296 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq4288
       have r₂ := eq26
       grind)
    | exact resolve eq4288 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4288
  have eq4299 : (σ x) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq4296
       have i₂ := eq1973 sF3
       grind)
    | exact superpose eq1973 eq4296
    | exact resolve eq4296 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4296
  have eq4301 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq4268 eq4299
    | exact resolve eq4299 eq4268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4268 eq4299
  have eq4302 : (σ x) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq4301
       have r₂ := eq27
       grind)
    | exact resolve eq4301 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4301
  have eq4309 : ∀ X0 X1 : G, (k X0 X0) = (M.op X1 (σ x)) ∨ (M.op x y) = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq4302 eq2168
    | exact resolve eq2168 eq4302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4311 : ∀ X0 : G, (σ x) = (k X0 X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq4302 eq2235
    | exact resolve eq2235 eq4302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4315 : ∀ X0 : G, (τ (σ x)) = (k X0 X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq4302 eq2288
    | exact resolve eq2288 eq4302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2288
  have eq4333 : ∀ X0 : G, x = (k X0 X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq30 eq4315
    | exact resolve eq4315 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4315
  have eq4336 : ∀ X1 : G, (σ x) = (M.op X1 (σ x)) ∨ (M.op x y) = (M.op y x) := by
    intro X1
    first
    | exact superpose eq4311 eq4309
    | exact resolve eq4309 eq4311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4309
  have eq4345 : (M.op x y) = (M.op y x) ∨ x = (σ x) := by
    first
    | exact superpose eq4311 eq4333
    | exact resolve eq4333 eq4311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4333
  have eq4356 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq4345
       grind)
    | exact superpose eq4345 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq4345
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq4345
       grind)
    | exact resolve eq12 eq4345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4345
  have eq4364 : x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ x = (σ x) := by
    first
    | (have r₁ := eq4356
       have r₂ := eq18
       grind)
    | exact resolve eq4356 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4356
  have eq4367 : (M.op x y) = (k x y) ∨ x = (k y y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq4364
       have i₂ := eq1973 y
       grind)
    | exact superpose eq1973 eq4364
    | exact resolve eq4364 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4364
  have eq5206 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq4336 eq4283
    | exact resolve eq4283 eq4336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4283 eq4336
  have eq5207 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5206
  have eq6297 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq4367
       grind)
    | exact superpose eq4367 eq41
    | exact resolve eq41 eq4367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4367
  have eq6298 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq6297
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6297
    | exact resolve eq6297 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6297
  have eq6300 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq6298
    | exact resolve eq6298 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6298
  have eq6876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (k y y) ∨ x = (σ x) := by
    first
    | exact superpose eq6300 eq1815
    | exact resolve eq1815 eq6300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6883 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (k y y) ∨ x = (σ x) := by
    first
    | (have r₁ := eq6876
       have r₂ := eq27
       grind)
    | exact resolve eq6876 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6876
  have eq7203 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ x = (σ x) := by
    first
    | exact superpose eq6883 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq6883
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq6883
       grind)
    | exact resolve eq12 eq6883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6883
  have eq7214 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ x = (σ x) := by
    first
    | (have r₁ := eq7203
       have r₂ := eq26
       grind)
    | exact resolve eq7203 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7203
  have eq7219 : (σ x) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq7214
       have i₂ := eq1973 sF3
       grind)
    | exact superpose eq1973 eq7214
    | exact resolve eq7214 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7214
  have eq7221 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (σ x) := by
    first
    | exact superpose eq6300 eq7219
    | exact resolve eq7219 eq6300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6300 eq7219
  have eq7223 : (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ x = (σ x) := by
    first
    | (have r₁ := eq7221
       have r₂ := eq27
       grind)
    | exact resolve eq7221 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7221
  have eq8461 : (τ (σ x)) = (k y y) ∨ x = (k y y) ∨ x = (σ x) := by
    first
    | exact superpose eq7223 eq116
    | exact resolve eq116 eq7223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq7223
  have eq8498 : x = (k y y) ∨ x = (k y y) ∨ x = (σ x) := by
    first
    | exact superpose eq30 eq8461
    | exact resolve eq8461 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8461
  have eq8499 : x = (k y y) ∨ x = (σ x) := by grind
  clear eq8498
  have eq8522 : ∀ X0 : G, x = (k X0 X0) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq2235 y X0
       have i₂ := eq8499
       grind)
    | exact superpose eq8499 eq2235
    | exact resolve eq2235 eq8499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8533 : ∀ X0 : G, (σ x) = (τ (k X0 X0)) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq2603 X0 y
       have i₂ := eq8499
       grind)
    | exact superpose eq8499 eq2603
    | exact resolve eq2603 eq8499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603 eq8499
  have eq8542 : ∀ X0 : G, (σ x) = (τ (k X0 X0)) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq8533 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8533
    | (have j0 := eq8533 X0
       grind)
    | exact resolve eq8533 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8533
  have eq8557 : (σ x) = (τ x) ∨ x = (σ x) := by
    first
    | exact superpose eq8522 eq8542
    | exact resolve eq8542 eq8522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8542
  have eq8980 : ∀ X0 : G, x = (τ (k X0 X0)) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq657 X0 X0
       have i₂ := eq8522 (τ X0)
       grind)
    | exact superpose eq8522 eq657
    | exact resolve eq657 eq8522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq9014 : x = (τ x) ∨ x = (σ x) := by
    first
    | exact superpose eq8522 eq8980
    | exact resolve eq8980 eq8522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8522 eq8980
  have eq9064 : x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq8557 eq9014
    | exact resolve eq9014 eq8557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8557 eq9014
  have eq9065 : x = (σ x) := by grind
  clear eq9064
  have eq9095 : (M.op x y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9065
       grind)
    | exact superpose eq9065 eq18
    | exact resolve eq18 eq9065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq9096 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq22
       have i₂ := eq9065
       grind)
    | exact superpose eq9065 eq22
    | exact resolve eq22 eq9065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq9102 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ x) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq283 X0 X1
       have i₂ := eq9065
       grind)
    | exact superpose eq9065 eq283
    | exact resolve eq283 eq9065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq9103 : (M.op x y) = (k (σ x) y) ∨ (M.op x y) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq1810
       have i₂ := eq9065
       grind)
    | exact superpose eq9065 eq1810
    | exact resolve eq1810 eq9065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1810
  have eq9104 : ∀ X0 X1 : G, (k X1 X1) = (M.op (σ x) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2124 X1 X0
       have i₂ := eq9065
       grind)
    | exact superpose eq9065 eq2124
    | exact resolve eq2124 eq9065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124
  have eq9108 : (M.op x y) = (M.op y (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5207
       have i₂ := eq9065
       grind)
    | exact superpose eq9065 eq5207
    | exact resolve eq5207 eq9065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5207
  have eq9112 : ∀ X0 X1 : G, (M.op X0 (k X1 X1)) = (M.op (σ x) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq9102 X0 X1
       have i₂ := eq1973 X1
       grind)
    | exact superpose eq1973 eq9102
    | exact resolve eq9102 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9102
  have eq9867 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq4311 x
       have i₂ := eq9104 X0 x
       grind)
    | exact superpose eq9104 eq4311
    | exact resolve eq4311 eq9104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4311 eq9104
  have eq9920 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op y (σ x)) := by
    intro X0
    first
    | (have i₁ := eq9867 X0
       have i₂ := eq9065
       grind)
    | exact superpose eq9065 eq9867
    | (have j0 := eq9867 X0
       grind)
    | exact resolve eq9867 eq9065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9867
  have eq13488 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ x) (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq4302 eq9112
    | exact resolve eq9112 eq4302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9112
  have eq13680 : ∀ X0 : G, (M.op x y) = (M.op y (σ x)) ∨ (M.op X0 (σ x)) = (M.op (σ x) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq13488 X0
       have i₂ := eq9065
       grind)
    | exact superpose eq9065 eq13488
    | (have j0 := eq13488 X0
       grind)
    | exact resolve eq13488 eq9065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13488
  have eq13722 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op x y) = (M.op y (σ x)) := by
    intro X0
    first
    | exact superpose eq9920 eq13680
    | exact resolve eq13680 eq9920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9920 eq13680
  have eq13804 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op y (σ x)) := by grind
  clear eq13722
  have eq633903 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq4302 eq2116
    | exact resolve eq2116 eq4302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4302
  have eq634842 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq633903
    | exact resolve eq633903 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633903
  have eq635077 : (M.op x y) = (M.op y (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq634842
       have i₂ := eq9065
       grind)
    | exact superpose eq9065 eq634842
    | exact resolve eq634842 eq9065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634842
  have eq635177 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y (σ x)) := by
    first
    | exact superpose eq9108 eq635077
    | exact resolve eq635077 eq9108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9108 eq635077
  have eq636784 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (M.op x y) = (M.op y (σ x)) := by
    first
    | exact superpose eq635177 eq153
    | exact resolve eq153 eq635177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq635177
  have eq636793 : x = (k x y) ∨ (M.op x y) = (M.op y (σ x)) := by
    first
    | exact superpose eq30 eq636784
    | exact resolve eq636784 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq636784
  have eq636801 : (σ x) = (k (σ x) y) ∨ (M.op x y) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq636793
       have i₂ := eq9065
       grind)
    | exact superpose eq9065 eq636793
    | exact resolve eq636793 eq9065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9065 eq636793
  have eq636808 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op y (σ x)) := by
    first
    | exact superpose eq9103 eq636801
    | exact resolve eq636801 eq9103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9103 eq636801
  have eq636815 : (M.op x y) = (M.op y (σ x)) := by
    first
    | (have r₁ := eq636808
       have r₂ := eq13804
       grind)
    | exact resolve eq636808 eq13804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13804 eq636808
  have eq636849 : (M.op x y) ≠ (M.op (σ x) y) ∨ (σ x) = (M.op y y) ∨ (M.op x y) = (k (σ x) y) := by
    first
    | exact superpose eq636815 eq12
    | (have j0 := eq12 (σ x) y
       grind)
    | exact resolve eq12 eq636815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636927 : (σ x) = (M.op y y) ∨ (M.op x y) = (k (σ x) y) := by
    first
    | (have r₁ := eq636849
       have r₂ := eq9095
       grind)
    | exact resolve eq636849 eq9095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636849
  have eq636955 : (σ x) = (k y y) ∨ (M.op x y) = (k (σ x) y) := by
    first
    | (have i₁ := eq636927
       have i₂ := eq1973 y
       grind)
    | exact superpose eq1973 eq636927
    | exact resolve eq636927 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636927
  have eq639887 : (k (σ x) y) = (M.op (σ x) y) ∨ (M.op x y) = (k (σ x) y) := by
    first
    | (have i₁ := eq2116 y
       have i₂ := eq636955
       grind)
    | exact superpose eq636955 eq2116
    | exact resolve eq2116 eq636955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2116 eq636955
  have eq640642 : (M.op x y) = (k (σ x) y) ∨ (M.op x y) = (k (σ x) y) := by
    first
    | exact superpose eq9095 eq639887
    | exact resolve eq639887 eq9095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9095 eq639887
  have eq640643 : (M.op x y) = (k (σ x) y) := by grind
  clear eq640642
  have eq640874 : (σ (M.op x y)) = (k (σ (σ x)) (σ y)) := by
    first
    | exact superpose eq640643 eq41
    | exact resolve eq41 eq640643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq640643
  have eq640879 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq9096 eq640874
    | exact resolve eq640874 eq9096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640874
  have eq640883 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq640879
    | exact resolve eq640879 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640879
  have eq640889 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq640883 eq1815
    | exact resolve eq1815 eq640883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815
  have eq640907 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq640889
       have r₂ := eq27
       grind)
    | exact resolve eq640889 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640889
  have eq640954 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq640907 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq640907
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq640907
       grind)
    | exact resolve eq12 eq640907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641034 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq640954
       have r₂ := eq26
       grind)
    | exact resolve eq640954 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq640954
  have eq641073 : (σ x) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq641034
       have i₂ := eq1973 sF3
       grind)
    | exact superpose eq1973 eq641034
    | exact resolve eq641034 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973 eq641034
  have eq641104 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq640883 eq641073
    | exact resolve eq641073 eq640883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640883 eq641073
  have eq641119 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq641104
       have r₂ := eq27
       grind)
    | exact resolve eq641104 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641104
  have eq641234 : ∀ X0 X1 : G, (k X0 X0) = (M.op X1 (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq641119 eq2168
    | exact resolve eq2168 eq641119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168
  have eq641236 : ∀ X0 : G, (σ x) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq641119 eq2235
    | exact resolve eq2235 eq641119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2235 eq641119
  have eq641937 : ∀ X1 : G, (σ x) = (M.op X1 (σ x)) := by
    intro X1
    first
    | (have i₁ := eq641234 x X1
       have i₂ := eq641236 x
       grind)
    | exact superpose eq641236 eq641234
    | exact resolve eq641234 eq641236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641234 eq641236
  have eq648734 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq641937 eq636815
    | exact resolve eq636815 eq641937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636815
  have eq649165 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq648734 eq9096
    | exact resolve eq9096 eq648734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9096
  have eq649524 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op x y)) := by
    first
    | exact superpose eq648734 eq640907
    | exact resolve eq640907 eq648734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640907
  have eq649525 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq648734 eq641937
    | exact resolve eq641937 eq648734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641937 eq648734
  have eq649527 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq649525 eq649524
    | exact resolve eq649524 eq649525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649524 eq649525
  have eq650434 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq649527 eq27
    | exact resolve eq27 eq649527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq649527
  have eq650582 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq649165 eq20
    | exact resolve eq20 eq649165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq649165
  have eq650600 : False := by grind
  exact eq650600

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxx_pxy_pyx_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (M.op X3 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X1
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X3 X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ (M.op X3 X3) ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = X1 ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X3 X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op X2 (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X2 X2) ∨ (M.op X2 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 X1 X2
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X2
       have i₂ := eq22 X0 X2
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 X0 X1 X2
       have i₂ := eq21 X0 X0 X1
       grind)
    | exact superpose eq21 eq87
    | exact resolve eq87 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq87
  have eq94 : ∀ X1 X2 : G, (M.op X2 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X1 X2
    first
    | (have j0 := eq82 x X1 X2
       grind)
    | (have r₁ := eq82 x X1 X1
       have r₂ := eq22 x X1
       grind)
    | exact resolve eq82 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq82
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X2 (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq80 X0 X1 X2 X3
       have i₂ := eq89 X0 X0
       grind)
    | exact superpose eq89 eq80
    | exact resolve eq80 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq89
  have eq107 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = X1 ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq26 X0 X1 X2 X3
       grind)
    | (have r₁ := eq26 X2 X1 X3 X0
       have r₂ := eq96 X0 X1 X2 X3
       grind)
    | exact resolve eq26 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq96
  have eq248 : ∀ X0 X3 X4 : G, X0 ≠ X0 ∨ (M.op X3 X3) = (k X3 X0) ∨ (k X4 X0) = (M.op X4 X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq24 x X0 x X3
       have i₂ := eq107 x X0 x X4
       grind)
    | exact superpose eq107 eq24
    | (have j0 := eq24 X0 X0 x X3
       have j1 := eq107 X0 X0 x X4
       grind)
    | (have r₁ := eq24 X0 x x X3
       have r₂ := eq107 X0 x x X3
       grind)
    | exact resolve eq24 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq107
  have eq266 : ∀ X0 X3 X4 : G, (M.op X3 X3) = (k X3 X0) ∨ (k X4 X0) = (M.op X4 X0) := by
    intro X0 X3 X4
    first
    | (have j0 := eq248 X0 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq655 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X2 X0) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92 X0 X1 X2
       have i₂ := eq94 X3 X0
       grind)
    | exact superpose eq94 eq92
    | (have j1 := eq94 X3 X0
       grind)
    | exact resolve eq92 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq94
  have eq883 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq266 X1 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq885 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq883 X0 X1
       have j1 := eq655 X1 X1 x X0
       grind)
    | (have r₁ := eq883 x X0
       have r₂ := eq655 X0 x x x
       grind)
    | (have r₁ := eq883 X1 X1
       have r₂ := eq655 X1 X1 X1 x
       grind)
    | exact resolve eq883 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq883
  have eq889 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq885 (σ X0) (σ X1)
       grind)
    | exact superpose eq885 eq15
    | exact resolve eq15 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq889 X0 X1
       have i₂ := eq885 X0 X1
       grind)
    | exact superpose eq885 eq889
    | exact resolve eq889 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885 eq889
  have eq900 : False := by grind
  exact eq900
