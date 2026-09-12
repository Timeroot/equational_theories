import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3897`: `x ◇ x = (y ◇ (z ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pyx_pyx_pxx_pyx_Equation3897 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3897 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3897.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq31 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X0 X1)) X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq44 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X0 X1)) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq31 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq31 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1 x
       have i₂ := eq9 X1 x X0
       grind)
    | exact superpose eq9 eq44
    | (have j0 := eq44 X0 X1 x
       grind)
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq93 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq97 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       have j1 := eq48 X1 X0
       grind)
    | (have r₁ := eq93 X1 X1
       have r₂ := eq48 X1 X1
       grind)
    | (have r₁ := eq93 X1 X0
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq93 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq93
  have eq209 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq97 (σ X1) (σ X0)
       grind)
    | exact superpose eq97 eq15
    | exact resolve eq15 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq209 X0 X1
       have i₂ := eq97 X1 X0
       grind)
    | exact superpose eq97 eq209
    | exact resolve eq209 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq209
  have eq219 : False := by grind
  exact eq219

/-- `Equation3897`: `x ◇ x = (y ◇ (z ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pxy_pyx_Equation3897 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3897 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3897.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq528 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op (σ X0) X1) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq22
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq22 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq532 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq684 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq532 x y
       grind)
    | exact superpose eq532 eq16
    | (have j1 := eq532 y x
       grind)
    | exact resolve eq16 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq532 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq532 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq3632 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq528 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq528
    | exact resolve eq528 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq3689 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3632 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq3632
    | (have j0 := eq3632 X0 X1
       grind)
    | exact resolve eq3632 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3632
  have eq3731 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq3689 X0 X1
       grind)
    | exact superpose eq3689 eq12
    | (have j1 := eq3689 X1 X0
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq3689 X0 X1
       grind)
    | exact resolve eq12 eq3689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3689
  have eq3761 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3731 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3731
  have eq3924 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq3761 X1 X0
       grind)
    | exact superpose eq3761 eq11
    | (have j1 := eq3761 X1 X0
       grind)
    | exact resolve eq11 eq3761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3761
  have eq4043 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3924 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3924
    | (have j0 := eq3924 X0 X1
       grind)
    | exact resolve eq3924 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3924
  have eq4049 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4043 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4043
    | (have j0 := eq4043 (σ X0) (σ X1)
       grind)
    | exact resolve eq4043 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4098 : ∀ X0 X1 : G, (τ X1) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq4043 X0 (τ X1)
       grind)
    | exact superpose eq4043 eq17
    | (have j1 := eq4043 X0 (τ X1)
       grind)
    | exact resolve eq17 eq4043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14721 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq692 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq692
    | (have j0 := eq692 (τ X1) (τ X0)
       grind)
    | exact resolve eq692 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq14784 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14721 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq14721
    | (have j0 := eq14721 X0 X1
       grind)
    | exact resolve eq14721 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14721
  have eq14811 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14784 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14784
    | (have j0 := eq14784 X0 X1
       grind)
    | exact resolve eq14784 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14784
  have eq14837 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14811 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14811
    | (have j0 := eq14811 X0 X1
       grind)
    | exact resolve eq14811 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14811
  have eq14861 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14837 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14837
    | (have j0 := eq14837 X0 X1
       grind)
    | exact resolve eq14837 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14837
  have eq14878 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14861 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14861
    | (have j0 := eq14861 X0 X1
       grind)
    | exact resolve eq14861 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14861
  have eq14891 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14878 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq14878
    | (have j0 := eq14878 X0 X1
       grind)
    | exact resolve eq14878 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14878
  have eq16077 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq4098 X1 X0
       grind)
    | exact superpose eq4098 eq17
    | (have j1 := eq4098 X1 X0
       grind)
    | exact resolve eq17 eq4098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4098
  have eq16235 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (k X0 (σ X1)) = X0 ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16077 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16077
    | (have j0 := eq16077 X0 X1
       grind)
    | exact resolve eq16077 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16077
  have eq16328 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16235 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16235
    | (have j0 := eq16235 (σ X0) X1
       grind)
    | exact resolve eq16235 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16235
  have eq16505 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16328 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq16328
    | (have j0 := eq16328 X0 X1
       grind)
    | exact resolve eq16328 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16328
  have eq16528 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16505 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq16505
    | (have j0 := eq16505 X0 X1
       grind)
    | exact resolve eq16505 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16505
  have eq16711 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq16528 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25109 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) ≠ (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq691 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq691
    | exact resolve eq691 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq25202 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25109 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq25109
    | (have j0 := eq25109 X0 X1
       grind)
    | exact resolve eq25109 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq25109
  have eq25216 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25202 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25202
    | exact resolve eq25202 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25202
  have eq45049 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4049 y x
       grind)
    | exact superpose eq4049 eq16
    | (have j1 := eq4049 y x
       grind)
    | exact resolve eq16 eq4049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4049
  have eq45239 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq45049
       have i₂ := eq16528 y x
       grind)
    | exact superpose eq16528 eq45049
    | (have j1 := eq16528 y x
       grind)
    | (have r₁ := eq45049
       have r₂ := eq16528 y x
       grind)
    | exact resolve eq45049 eq16528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45049
  have eq45240 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq45239
  have eq45247 : (M.op x y) = (M.op y x) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq16711 y x
       grind)
    | (have r₁ := eq45240
       have r₂ := eq16711 y x
       grind)
    | exact resolve eq45240 eq16711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45240
  have eq45256 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq45247
       grind)
    | exact superpose eq45247 eq12
    | exact resolve eq12 eq45247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45257 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq45247
       grind)
    | exact superpose eq45247 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq45247
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq45247
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq45247
       grind)
    | exact resolve eq13 eq45247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45247
  have eq45266 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq45257
  have eq45268 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq45256
       have r₂ := eq45266
       grind)
    | exact resolve eq45256 eq45266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45256 eq45266
  have eq45337 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq45268
       grind)
    | exact superpose eq45268 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq45268
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq45268
       grind)
    | exact resolve eq13 eq45268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45268
  have eq45344 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (k x y) := by grind
  clear eq45337
  have eq45352 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq45344
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq45344 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45344
  have eq45370 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq45352
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq45352
    | exact resolve eq45352 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45352
  have eq45384 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq45370
       grind)
    | exact superpose eq45370 eq16
    | exact resolve eq16 eq45370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45370
  have eq45489 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq45384
       have i₂ := eq16528 y x
       grind)
    | exact superpose eq16528 eq45384
    | (have j1 := eq16528 y x
       grind)
    | (have r₁ := eq45384
       have r₂ := eq16528 y x
       grind)
    | exact resolve eq45384 eq16528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16528 eq45384
  have eq45490 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq45489
  have eq45497 : (M.op x y) = (M.op y x) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq16711 y x
       grind)
    | (have r₁ := eq45490
       have r₂ := eq16711 y x
       grind)
    | exact resolve eq45490 eq16711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16711 eq45490
  have eq45747 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq45497
       grind)
    | exact superpose eq45497 eq12
    | exact resolve eq12 eq45497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45748 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq45497
       grind)
    | exact superpose eq45497 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq45497
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq45497
       grind)
    | exact resolve eq13 eq45497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45497
  have eq45757 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq45748
  have eq45758 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq45757
  have eq45759 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq45747
  have eq45761 : (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq45759
       have r₂ := eq45758
       grind)
    | exact resolve eq45759 eq45758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45758 eq45759
  have eq45775 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq4043 y x
       have i₂ := eq45761
       grind)
    | exact superpose eq45761 eq4043
    | (have j0 := eq4043 y x
       grind)
    | exact resolve eq4043 eq45761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4043
  have eq45827 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq25216 y x
       have i₂ := eq45761
       grind)
    | exact superpose eq45761 eq25216
    | (have j0 := eq25216 y x
       grind)
    | (have r₁ := eq25216 y x
       have r₂ := eq45761
       grind)
    | exact resolve eq25216 eq45761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25216
  have eq45867 : x = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq45827
  have eq45889 : x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq45775
  have eq45959 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq45867
  have eq45965 : (M.op x y) = (M.op y x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq45959
       have r₂ := eq45889
       grind)
    | exact resolve eq45959 eq45889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45889 eq45959
  have eq45979 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq45965
       grind)
    | exact superpose eq45965 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq45965
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq45965
       grind)
    | exact resolve eq13 eq45965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45965
  have eq45986 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq45979
  have eq45989 : (M.op x y) = (k y x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq45986
       have r₂ := eq12 y x
       grind)
    | exact resolve eq45986 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45986
  have eq45999 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq684
       have i₂ := eq45989
       grind)
    | exact superpose eq45989 eq684
    | exact resolve eq684 eq45989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq45989
  have eq46008 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq45999
  have eq46012 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq692 y x
       grind)
    | (have r₁ := eq46008
       have r₂ := eq692 x y
       grind)
    | exact resolve eq46008 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692 eq46008
  have eq46150 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46012
       grind)
    | exact superpose eq46012 eq16
    | exact resolve eq16 eq46012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46160 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq46012
       grind)
    | exact superpose eq46012 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq46012
       grind)
    | exact resolve eq12 eq46012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46012
  have eq46177 : (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq46160
  have eq46196 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq46177
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq46177
    | exact resolve eq46177 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46177
  have eq46251 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq46196
       grind)
    | exact superpose eq46196 eq12
    | exact resolve eq12 eq46196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46252 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq46196
       grind)
    | exact superpose eq46196 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq46196
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq46196
       grind)
    | exact resolve eq13 eq46196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46196
  have eq46261 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq46252
  have eq46269 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq46261
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq46261
    | exact resolve eq46261 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46261
  have eq46270 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq46251
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq46251
    | exact resolve eq46251 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46251
  have eq46287 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq46270
       have r₂ := eq46269
       grind)
    | exact resolve eq46270 eq46269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46269 eq46270
  have eq48450 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46287
       grind)
    | exact superpose eq46287 eq16
    | exact resolve eq16 eq46287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46287
  have eq48550 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq48450
       have i₂ := eq45761
       grind)
    | exact superpose eq45761 eq48450
    | exact resolve eq48450 eq45761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45761 eq48450
  have eq48567 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq48550
  have eq48568 : (σ y) = (σ (k y x)) := by grind
  clear eq48567
  have eq48593 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq48568
       grind)
    | exact superpose eq48568 eq10
    | exact resolve eq10 eq48568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48771 : y = (k y x) := by
    first
    | (have i₁ := eq48593
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq48593
    | exact resolve eq48593 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48593
  have eq48787 : y ≠ y ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14891 y x
       have i₂ := eq48771
       grind)
    | exact superpose eq48771 eq14891
    | (have j0 := eq14891 y x
       grind)
    | (have r₁ := eq14891 y x
       have r₂ := eq48771
       grind)
    | exact resolve eq14891 eq48771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14891
  have eq48799 : y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq48787
  have eq50786 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq46150
       have i₂ := eq48799
       grind)
    | exact superpose eq48799 eq46150
    | exact resolve eq46150 eq48799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50809 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq50786
  have eq58301 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq50809
       grind)
    | exact superpose eq50809 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq50809
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq50809
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq50809
       grind)
    | exact resolve eq13 eq50809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50809
  have eq58308 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq58301
  have eq58310 : (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq58308
       have r₂ := eq12 y x
       grind)
    | exact resolve eq58308 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58308
  have eq58318 : y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq58310
       have i₂ := eq48771
       grind)
    | exact superpose eq48771 eq58310
    | exact resolve eq58310 eq48771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58310
  have eq58327 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq46150
       have i₂ := eq58318
       grind)
    | exact superpose eq58318 eq46150
    | exact resolve eq46150 eq58318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46150 eq58318
  have eq58352 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq58327
  have eq58353 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq58352
  have eq58377 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq58353
       grind)
    | exact superpose eq58353 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq58353
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq58353
       grind)
    | exact resolve eq13 eq58353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58353
  have eq58384 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq58377
  have eq58392 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq58384
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq58384 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58384
  have eq58410 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq58392
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq58392
    | exact resolve eq58392 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58392
  have eq58412 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq58410
       have i₂ := eq48568
       grind)
    | exact superpose eq48568 eq58410
    | exact resolve eq58410 eq48568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48568 eq58410
  have eq58420 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58412
       grind)
    | exact superpose eq58412 eq16
    | exact resolve eq16 eq58412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58412
  have eq58504 : (σ y) ≠ (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq58420
       have i₂ := eq48799
       grind)
    | exact superpose eq48799 eq58420
    | exact resolve eq58420 eq48799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48799
  have eq58525 : (M.op x y) = (M.op y x) := by grind
  clear eq58504
  have eq58550 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq58525
       grind)
    | exact superpose eq58525 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq58525
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq58525
       grind)
    | exact resolve eq13 eq58525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58525
  have eq58557 : y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq58550
  have eq58559 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq58557
       have r₂ := eq12 y x
       grind)
    | exact resolve eq58557 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58557
  have eq58568 : y = (M.op x y) := by
    first
    | (have i₁ := eq58559
       have i₂ := eq48771
       grind)
    | exact superpose eq48771 eq58559
    | exact resolve eq58559 eq48771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48771 eq58559
  have eq58581 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq58420
       have i₂ := eq58568
       grind)
    | exact superpose eq58568 eq58420
    | exact resolve eq58420 eq58568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58420 eq58568
  have eq58603 : False := by grind
  exact eq58603

/-- `Equation3912`: `x ◇ x = (y ◇ (z ◇ w)) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pxx_pxy_Equation3912 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X3)) X3) := by
    intro X0 X1 X2 X3
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq176 : ∀ X0 X1 X2 X5 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X0)) X5) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq16 X1 X2 (M.op x (M.op x X5)) X5
       have i₂ := eq16 X0 x x X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op x y)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X5 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X5) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq16 X1 (M.op x (M.op x (M.op x X5))) x X5
       have i₂ := eq16 X0 x x (M.op x X5)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq16 X1 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X1 X2) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq181 X1 X0
       grind)
    | (have i₁ := eq13 X1 X2
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq13
    | (have j0 := eq13 X1 X2
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq181 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op x y)) y) = (M.op (M.op X2 (M.op x y)) y) := by
    intro X0 X2
    first
    | (have i₁ := eq177 x X2
       have i₂ := eq177 x X0
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 (M.op x y)) y) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X1 (M.op x X3) x X3
       have i₂ := eq177 (M.op x X3) X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq180 X3 x X4
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq180 X0 (M.op X0 X0) x
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op x y)) y) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq177 x X3
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq177 (M.op X0 X0) X1
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq177
    | exact resolve eq177 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq481 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq397 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq397
    | exact resolve eq397 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq1049 : ∀ X0 X1 X2 X4 : G, (M.op X2 X2) = (M.op (M.op (M.op (M.op X0 X0) X1) y) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq210 (M.op X0 X0) X1 x
       have i₂ := eq229 X0 sF0 x X4
       grind)
    | (have i₁ := eq210 (M.op x x) X1 x
       have i₂ := eq229 X0 X1 x sF0
       grind)
    | exact superpose eq229 eq210
    | exact resolve eq210 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq1051 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op x y)) y) = (M.op (M.op (M.op X0 X0) X1) y) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq197 (M.op X0 X0) x
       have i₂ := eq229 X0 sF0 X3 x
       grind)
    | (have i₁ := eq197 (M.op X3 X3) x
       have i₂ := eq229 X0 X1 X3 sF0
       grind)
    | exact superpose eq229 eq197
    | exact resolve eq197 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq1482 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 (M.op X0 X0) X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq1524 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (k (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 X0 X2 X1 X3
       have i₂ := eq1482 X0 X1
       grind)
    | exact superpose eq1482 eq176
    | exact resolve eq176 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1550 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X1 X2 (M.op X0 X0)
       have i₂ := eq1482 X0 (M.op X1 X1)
       grind)
    | exact superpose eq1482 eq180
    | exact resolve eq180 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1647 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op x y)) y) = (M.op (k (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq255 x (M.op x x) X3
       have i₂ := eq1524 X0 X1 (M.op x x) X2
       grind)
    | exact superpose eq1524 eq255
    | exact resolve eq255 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq1649 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X4) X5) = (M.op (k (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq229 x (M.op x x) X4 X5
       have i₂ := eq1524 X0 X1 (M.op x x) X2
       grind)
    | exact superpose eq1524 eq229
    | exact resolve eq229 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq1524
  have eq1696 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (k X3 X3) ∨ (M.op (M.op X0 (M.op X1 X2)) X2) = X3 ∨ (M.op (M.op X0 (M.op X1 X2)) X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq11
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1702 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq11
    | exact resolve eq11 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1740 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq181 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq181
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq181 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1793 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq1794 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq1796 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1797 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1796 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq1811 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1740 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740
  have eq1825 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1702 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1702
  have eq1831 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (k X3 X3) ∨ (M.op (M.op X0 (M.op X1 X2)) X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1696 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1696
  have eq2055 : ∀ X0 X1 : G, (k X1 X1) = (k X0 X0) ∨ (k X0 X0) = X1 ∨ (k X0 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq1811 X0 X1
       grind)
    | exact superpose eq1811 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq1811 X0 X1
       grind)
    | exact resolve eq11 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2083 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1797 X1
       have i₂ := eq1811 X1 X0
       grind)
    | exact superpose eq1811 eq1797
    | (have j0 := eq1797 X1
       have j1 := eq1811 X1 X1
       grind)
    | (have r₁ := eq1797 (M.op X1 X1)
       have r₂ := eq1811 (M.op X1 X1) X1
       grind)
    | exact resolve eq1797 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797
  have eq2093 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2083 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083
  have eq2094 : ∀ X0 X1 : G, (k X1 X1) = (k X0 X0) ∨ (k X0 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2055 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055
  have eq2119 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2093 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq2093
    | (have j0 := eq2093 X0 X1
       have j1 := eq11 X1 X1
       grind)
    | (have r₁ := eq2093 X1 (k X1 X1)
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq2093 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq2093 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq11 X0 (M.op X0 X0)
       grind)
    | exact resolve eq2093 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2131 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2119 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2119
  have eq2171 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (k X0 X0) X3) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq180 X2 X1 X3
       have i₂ := eq1825 X2 X0
       grind)
    | exact superpose eq1825 eq180
    | (have j1 := eq1825 X1 (M.op (k X0 X0) X3)
       grind)
    | exact resolve eq180 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq2174 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X1 X2
       have i₂ := eq1825 X2 X0
       grind)
    | exact superpose eq1825 eq181
    | (have j1 := eq1825 X1 X0
       grind)
    | exact resolve eq181 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2226 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq1825 X0 (σ X1)
       grind)
    | exact superpose eq1825 eq10
    | (have j1 := eq1825 X0 (σ (k X1 X1))
       grind)
    | exact resolve eq10 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2228 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq481 X1 X1
       have i₂ := eq1825 X0 (τ X1)
       grind)
    | exact superpose eq1825 eq481
    | (have j1 := eq1825 X0 (τ (k X1 X1))
       grind)
    | exact resolve eq481 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2229 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1825 X0 (τ X1)
       grind)
    | exact superpose eq1825 eq34
    | (have j1 := eq1825 X0 (τ X1)
       grind)
    | exact resolve eq34 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1825
  have eq2233 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2229 X0 X1
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq2229
    | (have j0 := eq2229 X0 X1
       grind)
    | exact resolve eq2229 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229
  have eq2356 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq2174 (σ X1) X0 X2
       grind)
    | exact superpose eq2174 eq10
    | (have j1 := eq2174 (σ (k X1 X1)) X1 X0
       grind)
    | exact resolve eq10 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2358 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (τ (k X1 X1)) ∨ (τ X1) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq481 X1 X1
       have i₂ := eq2174 (τ X1) X0 X2
       grind)
    | exact superpose eq2174 eq481
    | (have j1 := eq2174 (τ (k X1 X1)) X1 X0
       grind)
    | exact resolve eq481 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq8873 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1793
       grind)
    | exact superpose eq1793 eq40
    | exact resolve eq40 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1793
  have eq8874 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8873
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8873
    | exact resolve eq8873 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8873
  have eq8876 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq8874
    | exact resolve eq8874 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8874
  have eq20430 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X4)) X4) = X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X1 X2 X3 X4
       have i₂ := eq1831 X2 X3 X4 X0
       grind)
    | exact superpose eq1831 eq16
    | (have j1 := eq1831 X2 X3 X4 X0
       grind)
    | exact resolve eq16 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20548 : ∀ X0 X1 X2 X3 : G, (k X3 X3) ≠ X3 ∨ (M.op (M.op X0 (M.op X1 X2)) X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1831 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831
  have eq42343 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq2171 X1 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171
  have eq42399 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X2) ≠ X3 ∨ (M.op X4 X4) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq42343 X4 X3 (k X3 X3)
       have i₂ := eq16 (k X3 X3) X0 X1 X2
       grind)
    | exact superpose eq16 eq42343
    | (have j0 := eq42343 X4 X3 X2
       grind)
    | (have r₁ := eq42343 X0 (M.op (M.op X1 (M.op X2 X3)) X3) (k (M.op (M.op X1 (M.op X2 X3)) X3) (M.op (M.op X1 (M.op X2 X3)) X3))
       have r₂ := eq16 (k (M.op (M.op X1 (M.op X2 X3)) X3) (M.op (M.op X1 (M.op X2 X3)) X3)) X1 X2 X3
       grind)
    | exact resolve eq42343 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42407 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42343 X2 X1 (k X1 X1)
       have i₂ := eq181 (k X1 X1) X0
       grind)
    | (have i₁ := eq42343 X2 X1 (k X1 X1)
       have i₂ := eq181 X0 (k X1 X1)
       grind)
    | exact superpose eq181 eq42343
    | (have j0 := eq42343 X2 X1 X2
       grind)
    | (have r₁ := eq42343 X0 (M.op X1 X1) (k (M.op X1 X1) (M.op X1 X1))
       have r₂ := eq181 (k (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq42343 X0 (M.op X0 X0) (k (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq181 X0 (k (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq42343 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42441 : ∀ X0 X1 X2 X3 : G, (k X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 ∨ (M.op X3 X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq42343 X2 X1 (k X1 X1)
       have i₂ := eq2174 X0 (k X1 X1) X3
       grind)
    | exact superpose eq2174 eq42343
    | (have j0 := eq42343 X2 X1 X2
       have j1 := eq2174 X1 X1 X2
       grind)
    | (have r₁ := eq42343 X0 (k X0 X0) (k (k X0 X0) (k X0 X0))
       have r₂ := eq2174 X0 (k (k X0 X0) (k X0 X0)) X2
       grind)
    | (have r₁ := eq42343 X0 X0 (k X0 X0)
       have r₂ := eq2174 X0 X1 (k X0 X0)
       grind)
    | (have r₁ := eq42343 X0 (M.op X2 X2) X2
       have r₂ := eq2174 (M.op (k (M.op X2 X2) (M.op X2 X2)) X2) X1 X2
       grind)
    | exact resolve eq42343 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42343
  have eq50331 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2226 X1 (M.op X2 X2)
       have i₂ := eq1550 X2 X2 X0
       grind)
    | exact superpose eq1550 eq2226
    | (have j0 := eq2226 X1 (M.op X0 X0)
       grind)
    | exact resolve eq2226 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550 eq2226
  have eq51225 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq2233 X0 (σ X1)
       grind)
    | exact superpose eq2233 eq10
    | (have j1 := eq2233 X0 (σ X1)
       grind)
    | exact resolve eq10 eq2233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2233
  have eq51401 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51225 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq51225
    | (have j0 := eq51225 X0 X1
       grind)
    | exact resolve eq51225 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51225
  have eq64791 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X1) = X2 ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51401 X0 X2
       have i₂ := eq51401 X1 X2
       grind)
    | exact superpose eq51401 eq51401
    | (have j0 := eq51401 X1 X2
       have j1 := eq51401 X1 X2
       grind)
    | exact resolve eq51401 eq51401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51401
  have eq65216 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq64791 X0 X1 X2
       have j1 := eq42407 X0 X2 X1
       grind)
    | (have r₁ := eq64791 X0 X0 X1
       have r₂ := eq42407 X0 X1 X2
       grind)
    | (have r₁ := eq64791 X0 X1 (M.op X0 X0)
       have r₂ := eq42407 X0 (M.op X1 X1) X2
       grind)
    | (have r₁ := eq64791 X0 X1 X1
       have r₂ := eq42407 X0 X1 X2
       grind)
    | exact resolve eq64791 eq42407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64791
  have eq75107 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X1 X1)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq65216 X0 X1 (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75108 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq65216 X0 X0 (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65216
  have eq75111 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq75108 X0 x
       have j1 := eq50331 X0 X0 X0
       grind)
    | (have r₁ := eq75108 x X0
       have r₂ := eq50331 X0 x x
       grind)
    | (have r₁ := eq75108 x x
       have r₂ := eq50331 X0 x x
       grind)
    | exact resolve eq75108 eq50331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75108
  have eq75112 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq75107 X0 X1
       have j1 := eq50331 X0 X1 X0
       grind)
    | (have r₁ := eq75107 X0 X0
       have r₂ := eq50331 X0 X0 x
       grind)
    | (have r₁ := eq75107 X0 x
       have r₂ := eq50331 X0 x x
       grind)
    | exact resolve eq75107 eq50331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50331 eq75107
  have eq75458 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op X0 X0)
       have i₂ := eq75111 X0
       grind)
    | exact superpose eq75111 eq15
    | exact resolve eq15 eq75111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75862 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq75112 (k (M.op x x) x) X1
       have i₂ := eq1647 x x (k (M.op x x) x) X0
       grind)
    | exact superpose eq1647 eq75112
    | exact resolve eq75112 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76163 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) y) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1647 x x (k (M.op x x) x) X1
       have i₂ := eq75112 X0 (k (M.op x x) x)
       grind)
    | exact superpose eq75112 eq1647
    | exact resolve eq1647 eq75112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq76180 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X1 X1)
       have i₂ := eq75112 X1 X0
       grind)
    | exact superpose eq75112 eq15
    | exact resolve eq15 eq75112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77150 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (τ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76180 (k (M.op x x) x) X2
       have i₂ := eq1649 x x (k (M.op x x) x) X0 X1
       grind)
    | exact superpose eq1649 eq76180
    | exact resolve eq76180 eq1649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649 eq76180
  have eq101032 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1794 eq8876
    | exact resolve eq8876 eq1794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794 eq8876
  have eq101047 : y = (M.op y y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq101032
       have r₂ := eq27
       grind)
    | exact resolve eq101032 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101032
  have eq101054 : y = (M.op y y) ∨ x = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1811 eq101047
    | (have j1 := eq1811 y x
       grind)
    | exact resolve eq101047 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101047
  have eq101057 : (σ y) = (k (σ x) (σ x)) ∨ x = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1811 eq101054
    | (have j1 := eq1811 y x
       grind)
    | exact resolve eq101054 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811 eq101054
  have eq101589 : (τ (σ y)) = (k x x) ∨ x = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq101057 eq97
    | exact resolve eq97 eq101057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101611 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ y)) ∨ (M.op X1 X1) = (τ (σ x)) ∨ x = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq101057 eq2358
    | (have j0 := eq2358 X0 (σ y) X0
       grind)
    | exact resolve eq2358 eq101057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2358 eq101057
  have eq101625 : ∀ X0 X1 : G, (M.op X0 X0) = y ∨ (M.op X1 X1) = (τ (σ x)) ∨ x = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq31 eq101611
    | (have j0 := eq101611 X0 X1
       grind)
    | exact resolve eq101611 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101611
  have eq101643 : y = (k x x) ∨ x = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31 eq101589
    | exact resolve eq101589 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq101589
  have eq101647 : ∀ X1 : G, (M.op X1 X1) = (τ (σ x)) ∨ x = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X1
    first
    | (have j0 := eq101625 y X1
       have j1 := eq2093 x y
       grind)
    | (have r₁ := eq101625 x X1
       have r₂ := eq2093 x y
       grind)
    | (have r₁ := eq101625 x x
       have r₂ := eq2093 x (τ (σ x))
       grind)
    | (have r₁ := eq101625 x X1
       have r₂ := eq2093 y y
       grind)
    | exact resolve eq101625 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093 eq101625
  have eq101658 : y = (k (σ x) (σ x)) ∨ x = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2094 eq101643
    | (have j1 := eq2094 (σ x) y
       grind)
    | exact resolve eq101643 eq2094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094 eq101643
  have eq101661 : ∀ X1 : G, (M.op X1 X1) = x ∨ x = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X1
    first
    | exact superpose eq29 eq101647
    | exact resolve eq101647 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101647
  have eq101672 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (k (σ x) (σ x)) := by
    first
    | (have j1 := eq2131 (σ x) (σ x)
       grind)
    | (have r₁ := eq101658
       have r₂ := eq2131 (σ x) y
       grind)
    | (have r₁ := eq101658
       have r₂ := eq2131 (σ x) x
       grind)
    | exact resolve eq101658 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131 eq101658
  have eq101674 : ∀ X1 : G, (M.op X1 X1) = x ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X1
    first
    | (have j0 := eq101661 X1
       have j1 := eq42441 x x X1 X1
       grind)
    | (have r₁ := eq101661 X1
       have r₂ := eq42441 (σ x) x x x
       grind)
    | exact resolve eq101661 eq42441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42441 eq101661
  have eq101681 : ∀ X1 : G, (σ x) = (k x x) ∨ y = (M.op y y) ∨ (M.op X1 X1) = x := by
    intro X1
    first
    | exact superpose eq2174 eq101674
    | (have j0 := eq101674 X1
       have j1 := eq2174 y X1 y
       grind)
    | exact resolve eq101674 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174 eq101674
  have eq101701 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 X0) = (σ x) ∨ x = (k (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq101672 eq181
    | exact resolve eq181 eq101672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101808 : (σ x) = (τ (σ x)) ∨ y = (M.op y y) ∨ x = (k (σ x) (σ x)) := by
    first
    | exact superpose eq101672 eq75458
    | exact resolve eq75458 eq101672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75458 eq101672
  have eq101903 : y = (M.op y y) ∨ x = (σ x) ∨ x = (k (σ x) (σ x)) := by
    first
    | exact superpose eq29 eq101808
    | exact resolve eq101808 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101808
  have eq102227 : y = (σ y) ∨ x = (σ x) ∨ x = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq75111 y
       have i₂ := eq101903
       grind)
    | exact superpose eq101903 eq75111
    | exact resolve eq75111 eq101903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102228 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ x = (σ x) ∨ x = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq75112 y X0
       have i₂ := eq101903
       grind)
    | exact superpose eq101903 eq75112
    | exact resolve eq75112 eq101903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75112 eq101903
  have eq102292 : ∀ X0 : G, x = (k (σ x) (σ x)) ∨ x = (σ x) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq102228 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq102228
    | (have j0 := eq102228 X0
       grind)
    | exact resolve eq102228 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102228
  have eq102293 : x = (k (σ x) (σ x)) ∨ x = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq102227
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq102227
    | exact resolve eq102227 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102227
  have eq102603 : (k x x) = (τ x) ∨ x = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq102293 eq97
    | exact resolve eq97 eq102293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq102293
  have eq102826 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ x)) ∨ (M.op X1 X1) = (σ x) ∨ x = (σ x) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq2356 X0 x X1
       have i₂ := eq102603
       grind)
    | exact superpose eq102603 eq2356
    | (have j0 := eq2356 X0 (τ x) X0
       grind)
    | exact resolve eq2356 eq102603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2356 eq102603
  have eq102837 : ∀ X0 X1 : G, (M.op X0 X0) = x ∨ (M.op X1 X1) = (σ x) ∨ x = (σ x) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq102826 X0 X1
       have i₂ := eq14 x
       grind)
    | exact superpose eq14 eq102826
    | (have j0 := eq102826 X0 X1
       grind)
    | exact resolve eq102826 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102826
  have eq102853 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = x ∨ x = (σ x) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq102837 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102837
    | (have j0 := eq102837 X0 X1
       grind)
    | exact resolve eq102837 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102837
  have eq110212 : ∀ X0 X1 X2 X3 : G, x ≠ (σ x) ∨ x = (M.op (M.op X0 (M.op X1 X2)) X2) ∨ y = (M.op y y) ∨ x = (M.op X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20548 X0 X1 X2 x
       have i₂ := eq101681 X3
       grind)
    | exact superpose eq101681 eq20548
    | (have j0 := eq20548 X0 X1 X2 x
       have j1 := eq101681 X3
       grind)
    | exact resolve eq20548 eq101681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20548 eq101681
  have eq110220 : ∀ X3 : G, x ≠ (σ x) ∨ y = (M.op y y) ∨ x = (M.op X3 X3) := by
    intro X3
    first
    | (have j0 := eq110212 x x x X3
       have j1 := eq42399 x x x y y
       grind)
    | (have r₁ := eq110212 x x x X3
       have r₂ := eq42399 x x x x x
       grind)
    | exact resolve eq110212 eq42399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42399 eq110212
  have eq110397 : ∀ X0 : G, y = (σ y) ∨ (M.op X0 X0) = (σ x) ∨ x = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq75111 y
       have i₂ := eq101701 X0
       grind)
    | exact superpose eq101701 eq75111
    | (have j1 := eq101701 X0
       grind)
    | exact resolve eq75111 eq101701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101701
  have eq110498 : ∀ X0 : G, x = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq110397 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq110397
    | (have j0 := eq110397 X0
       grind)
    | exact resolve eq110397 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110397
  have eq110792 : ∀ X0 X1 : G, (M.op X0 X0) = (τ x) ∨ (M.op X0 X0) = (τ (σ x)) ∨ (M.op X1 X1) = (σ x) ∨ y = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq110498 eq2228
    | (have j0 := eq2228 X0 x
       have j1 := eq110498 X1
       grind)
    | exact resolve eq2228 eq110498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228 eq110498
  have eq110812 : ∀ X0 X1 : G, (M.op X0 X0) = x ∨ (M.op X0 X0) = (τ x) ∨ (M.op X1 X1) = (σ x) ∨ y = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq29 eq110792
    | (have j0 := eq110792 X0 X1
       grind)
    | exact resolve eq110792 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110792
  have eq110832 : ∀ X0 X1 : G, (M.op X0 X0) = x ∨ (M.op X0 X0) = (τ (σ x)) ∨ (M.op X1 X1) = (σ x) ∨ y = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq102853 eq110812
    | (have j0 := eq110812 X0 X1
       have j1 := eq102853 X0 X1
       grind)
    | exact resolve eq110812 eq102853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102853 eq110812
  have eq110845 : ∀ X0 X1 : G, (M.op X0 X0) = x ∨ (M.op X0 X0) = x ∨ (M.op X1 X1) = (σ x) ∨ y = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq29 eq110832
    | (have j0 := eq110832 X0 X1
       grind)
    | exact resolve eq110832 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110832
  have eq110846 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = x ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq110845 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110845
  have eq118624 : ∀ X0 X2 : G, (M.op X0 X0) = (τ (σ x)) ∨ x = (M.op X2 X2) ∨ y = (σ y) := by
    intro X0 X2
    first
    | (have i₁ := eq77150 x (M.op x x) X0
       have i₂ := eq110846 X2 (M.op x x)
       grind)
    | (have i₁ := eq77150 X0 (M.op X0 X0) X2
       have i₂ := eq110846 (M.op X0 X0) x
       grind)
    | exact superpose eq110846 eq77150
    | (have j1 := eq110846 X2 x
       grind)
    | exact resolve eq77150 eq110846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77150 eq110846
  have eq118734 : ∀ X0 X2 : G, (M.op X0 X0) = x ∨ x = (M.op X2 X2) ∨ y = (σ y) := by
    intro X0 X2
    first
    | exact superpose eq29 eq118624
    | (have j0 := eq118624 X0 X0
       grind)
    | exact resolve eq118624 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118624
  have eq119137 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (σ y) := by
    intro X0
    first
    | (have j0 := eq118734 X0 X0
       have j1 := eq42407 X0 x X0
       grind)
    | (have r₁ := eq118734 X0 x
       have r₂ := eq42407 X0 x x
       grind)
    | (have r₁ := eq118734 X0 X0
       have r₂ := eq42407 X0 x x
       grind)
    | exact resolve eq118734 eq42407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42407 eq118734
  have eq119700 : x = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq75111 x
       have i₂ := eq119137 x
       grind)
    | exact superpose eq119137 eq75111
    | exact resolve eq75111 eq119137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119711 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op x y)) y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq76163 x X0
       have i₂ := eq119137 x
       grind)
    | exact superpose eq119137 eq76163
    | exact resolve eq76163 eq119137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76163
  have eq119833 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq75862 sF0 x
       have i₂ := eq119137 sF0
       grind)
    | exact superpose eq119137 eq75862
    | exact resolve eq75862 eq119137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75862
  have eq119881 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op (M.op x y) X2) ∨ y = (σ y) := by
    intro X0 X2
    first
    | (have i₁ := eq1049 x (M.op x x) X0 X2
       have i₂ := eq119137 (M.op x x)
       grind)
    | exact superpose eq119137 eq1049
    | exact resolve eq1049 eq119137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq119882 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1051 x (M.op x x) X0
       have i₂ := eq119137 (M.op x x)
       grind)
    | exact superpose eq119137 eq1051
    | exact resolve eq1051 eq119137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq120021 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq119882 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119882
    | (have j0 := eq119882 X0
       grind)
    | exact resolve eq119882 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119882
  have eq120022 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op (M.op x y) X2) ∨ y = (σ y) := by
    intro X0 X2
    first
    | (have i₁ := eq119881 X0 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119881
    | (have j0 := eq119881 X0 X2
       grind)
    | exact resolve eq119881 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119881
  have eq120059 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq119833 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119833
    | (have j0 := eq119833 X0
       grind)
    | exact resolve eq119833 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119833
  have eq120141 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op x y)) y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq119711 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq119711
    | (have j0 := eq119711 X0
       grind)
    | exact resolve eq119711 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119711
  have eq120151 : y = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq119700
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq119700
    | exact resolve eq119700 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119700
  have eq120363 : ∀ X2 : G, x = (M.op (M.op x y) X2) ∨ y = (σ y) := by
    intro X2
    first
    | exact superpose eq119137 eq120022
    | exact resolve eq120022 eq119137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120022
  have eq120388 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq120059
    | (have j0 := eq120059 X0
       grind)
    | exact resolve eq120059 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120059
  have eq120437 : (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq120021 eq120141
    | exact resolve eq120141 eq120021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120021 eq120141
  have eq120593 : ∀ X2 : G, (σ x) = (M.op (M.op x y) X2) ∨ y = (σ y) := by
    intro X2
    first
    | exact superpose eq120151 eq120363
    | exact resolve eq120363 eq120151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120363
  have eq120604 : x = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq119137 eq120388
    | exact resolve eq120388 eq119137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119137 eq120388
  have eq120698 : ∀ X2 : G, (M.op x y) = (M.op (M.op x y) X2) ∨ y = (σ y) := by
    intro X2
    first
    | exact superpose eq120437 eq120593
    | exact resolve eq120593 eq120437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120593
  have eq120703 : (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq120151 eq120604
    | exact resolve eq120604 eq120151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120151 eq120604
  have eq120751 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq120437 eq120703
    | exact resolve eq120703 eq120437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120703
  have eq120874 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq120437 eq26
    | exact resolve eq26 eq120437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120437
  have eq121029 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq120698 eq120874
    | exact resolve eq120874 eq120698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120698 eq120874
  have eq121269 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq121029 eq27
    | exact resolve eq27 eq121029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121029
  have eq121335 : y = (σ y) := by
    first
    | (have r₁ := eq121269
       have r₂ := eq120751
       grind)
    | exact resolve eq121269 eq120751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120751 eq121269
  have eq121363 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq121335
       grind)
    | exact superpose eq121335 eq18
    | exact resolve eq18 eq121335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq121364 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq121335
       grind)
    | exact superpose eq121335 eq24
    | exact resolve eq24 eq121335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq121367 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq121335
       grind)
    | exact superpose eq121335 eq177
    | exact resolve eq177 eq121335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq121501 : ∀ X0 : G, (τ (k (σ y) X0)) = (k (σ y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq121364 eq454
    | exact resolve eq454 eq121364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq121724 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op x y)) (σ y)) = X1 ∨ (M.op X2 X2) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq121363 eq20430
    | (have j0 := eq20430 X1 X2 X2 x x
       grind)
    | exact resolve eq20430 eq121363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20430
  have eq124981 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (σ y)) = (σ (M.op (M.op X0 (M.op x y)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq75111 X0
       have i₂ := eq121367 X0 x
       grind)
    | exact superpose eq121367 eq75111
    | exact resolve eq75111 eq121367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121367
  have eq261458 : ∀ X0 X2 : G, (M.op X2 X2) = (k X0 X0) ∨ (σ X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq124981 X0
       have i₂ := eq121724 X0 (M.op (M.op X0 sF0) sF3) X2
       grind)
    | exact superpose eq121724 eq124981
    | (have j1 := eq121724 X0 X0 X2
       grind)
    | exact resolve eq124981 eq121724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121724
  have eq262083 : ∀ X0 : G, (k X0 X0) = (σ (k X0 X0)) ∨ (σ X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq75111 x
       have i₂ := eq261458 X0 x
       grind)
    | exact superpose eq261458 eq75111
    | (have j1 := eq261458 (k X0 X0) x
       grind)
    | exact resolve eq75111 eq261458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75111 eq261458
  have eq265648 : (k x x) = (k (σ x) (σ x)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq262083 x
       grind)
    | exact superpose eq262083 eq39
    | (have j1 := eq262083 x
       grind)
    | exact resolve eq39 eq262083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265799 : (k x x) = (k (σ x) (σ x)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq265648
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq265648
    | exact resolve eq265648 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265648
  have eq265945 : (k x x) = (k (σ x) (σ x)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq265799
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq265799
    | exact resolve eq265799 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265799
  have eq266272 : (k (σ x) (σ x)) = (σ (k (σ x) (σ x))) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | (have i₁ := eq262083 x
       have i₂ := eq265945
       grind)
    | exact superpose eq265945 eq262083
    | (have j0 := eq262083 (σ x)
       grind)
    | exact resolve eq262083 eq265945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262083 eq265945
  have eq266288 : x = (σ x) ∨ (k (σ x) (σ x)) = (σ (k (σ x) (σ x))) ∨ x = (σ x) := by
    first
    | (have i₁ := eq266272
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq266272
    | exact resolve eq266272 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266272
  have eq266289 : (k (σ x) (σ x)) = (σ (k (σ x) (σ x))) ∨ x = (σ x) := by grind
  clear eq266288
  have eq266323 : ∀ X0 : G, x = (σ x) ∨ x = (σ x) ∨ x = (σ x) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq102292 eq266289
    | (have j1 := eq102292 X0
       grind)
    | exact resolve eq266289 eq102292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102292 eq266289
  have eq266432 : ∀ X0 : G, x = (σ x) ∨ x = (σ x) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq266323 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266323
  have eq266502 : ∀ X0 : G, x = (σ x) ∨ x = (σ x) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq266432 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq266432
    | (have j0 := eq266432 X0
       grind)
    | exact resolve eq266432 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq266432
  have eq266503 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq266502 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266502
  have eq266884 : ∀ X1 : G, (k (σ y) X1) = (M.op X1 (σ y)) ∨ x = (σ x) := by
    intro X1
    first
    | (have i₁ := eq1482 x X1
       have i₂ := eq266503 x
       grind)
    | exact superpose eq266503 eq1482
    | exact resolve eq1482 eq266503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266503
  have eq270146 : (M.op x y) = (k (σ y) x) ∨ x = (σ x) := by
    first
    | exact superpose eq266884 eq121363
    | exact resolve eq121363 eq266884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270157 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (σ x) := by
    first
    | exact superpose eq266884 eq26
    | (have j1 := eq266884 (σ x)
       grind)
    | exact resolve eq26 eq266884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266884
  have eq271844 : (τ (M.op (σ x) (σ y))) = (k (σ y) (τ (σ x))) ∨ x = (σ x) := by
    first
    | exact superpose eq270157 eq121501
    | exact resolve eq121501 eq270157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121501 eq270157
  have eq271852 : (τ (M.op (σ x) (σ y))) = (k (σ y) x) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq271844
    | exact resolve eq271844 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq271844
  have eq271860 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (σ x) := by
    first
    | exact superpose eq270146 eq271852
    | exact resolve eq271852 eq270146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270146 eq271852
  have eq271867 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq271860 eq14
    | exact resolve eq14 eq271860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271860
  have eq271928 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq271867
    | exact resolve eq271867 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271867
  have eq271929 : x = (σ x) := by
    first
    | (have r₁ := eq271928
       have r₂ := eq27
       grind)
    | exact resolve eq271928 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271928
  have eq279940 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq271929
       grind)
    | exact superpose eq271929 eq39
    | exact resolve eq39 eq271929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq279965 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq110220 x
       have i₂ := eq271929
       grind)
    | exact superpose eq271929 eq110220
    | (have r₁ := eq110220 x
       have r₂ := eq271929
       grind)
    | exact resolve eq110220 eq271929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110220
  have eq279986 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq121363
       have i₂ := eq271929
       grind)
    | exact superpose eq271929 eq121363
    | exact resolve eq121363 eq271929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121363 eq271929
  have eq279994 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq279965 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279965
  have eq279995 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq279994 X0
       have i₂ := eq121335
       grind)
    | exact superpose eq121335 eq279994
    | (have j0 := eq279994 X0
       grind)
    | exact resolve eq279994 eq121335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121335 eq279994
  have eq280378 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq279986 eq26
    | exact resolve eq26 eq279986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280419 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq280378 eq27
    | exact resolve eq27 eq280378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq284355 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 X0
       have i₂ := eq279995 X0
       grind)
    | exact superpose eq279995 eq181
    | (have j1 := eq279995 X1
       grind)
    | exact resolve eq181 eq279995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq279995
  have eq285514 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq124981 sF0
       have i₂ := eq284355 X0 sF0
       grind)
    | (have i₁ := eq124981 sF0
       have i₂ := eq284355 sF0 x
       grind)
    | exact superpose eq284355 eq124981
    | (have j1 := eq284355 X0 x
       grind)
    | exact resolve eq124981 eq284355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124981 eq284355
  have eq285931 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq26 eq285514
    | (have j0 := eq285514 X0
       grind)
    | exact resolve eq285514 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq285514
  have eq286499 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq280378 eq285931
    | (have j0 := eq285931 X0
       grind)
    | exact resolve eq285931 eq280378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280378 eq285931
  have eq286900 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq286499
    | (have j0 := eq286499 X0
       grind)
    | exact resolve eq286499 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286499
  have eq287141 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq286900 X0
       grind)
    | (have r₁ := eq286900 X0
       have r₂ := eq280419
       grind)
    | exact resolve eq286900 eq280419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286900
  have eq287554 : ∀ X1 : G, (k (σ y) X1) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq1482 x X1
       have i₂ := eq287141 x
       grind)
    | exact superpose eq287141 eq1482
    | exact resolve eq1482 eq287141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482 eq287141
  have eq291220 : (M.op x y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq287554 eq279986
    | exact resolve eq279986 eq287554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279986 eq287554
  have eq293248 : (σ (M.op x y)) = (k (σ (σ y)) (σ x)) := by
    first
    | exact superpose eq291220 eq279940
    | exact resolve eq279940 eq291220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279940
  have eq293252 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq121364 eq293248
    | exact resolve eq293248 eq121364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121364 eq293248
  have eq293263 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq291220 eq293252
    | exact resolve eq293252 eq291220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291220 eq293252
  have eq293283 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq293263 eq20
    | exact resolve eq20 eq293263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq293263
  have eq293429 : False := by grind
  exact eq293429

/-- `Equation3912`: `x ◇ x = (y ◇ (z ◇ w)) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pyy_pyx_pxy_Equation3912 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X3)) X3) := by
    intro X0 X1 X2 X3
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
  have eq50 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (M.op (M.op X4 (M.op X5 X6)) X6) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq14 x X4 X5 X6
       have i₂ := eq14 x X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X3) = (M.op (M.op X4 (M.op (M.op X0 (M.op X1 X2)) X2)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X3 X4 X5 X5
       have i₂ := eq14 X5 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op x y)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X5 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X5) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq14 X1 (M.op x (M.op x (M.op x X5))) x X5
       have i₂ := eq14 X0 x x (M.op x X5)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq57 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq13
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq57 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq57 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq103 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq36
  have eq144 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq167 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq144 eq16
    | exact resolve eq16 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X2 X2) = X2 ∨ (k (M.op X1 X1) X2) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X1) X2
       have i₂ := eq56 X1 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq56 X0 X1 x
       grind)
    | exact superpose eq56 eq12
    | (have j0 := eq12 (M.op X1 X1) X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X0) x) X1
       have r₂ := eq56 X0 (M.op (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq56 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq12 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq56 X0 X1 x
       grind)
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq56 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq56 eq13
    | (have r₁ := eq13 X0 (M.op (M.op X0 X0) x)
       have r₂ := eq56 X0 (M.op (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq56 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq294 X0 X1 X2
       grind)
    | (have r₁ := eq294 X0 X1 X2
       have r₂ := eq57 X0 X1
       grind)
    | (have r₁ := eq294 X1 X0 X2
       have r₂ := eq57 X0 X1
       grind)
    | exact resolve eq294 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq305 : ∀ X1 X2 : G, (k (M.op X1 X1) X2) = (M.op X2 (M.op X1 X1)) ∨ (M.op X2 X2) = X2 := by
    intro X1 X2
    first
    | (have j0 := eq293 x X1 X2
       grind)
    | (have r₁ := eq293 x X1 X2
       have r₂ := eq57 x X1
       grind)
    | (have r₁ := eq293 X1 x X2
       have r₂ := eq57 x X1
       grind)
    | exact resolve eq293 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq345 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : ∀ X0 X1 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 X6)) X6) = (M.op (M.op (M.op X0 X0) X1) X3) := by
    intro X0 X1 X3 X4 X5 X6
    first
    | (have i₁ := eq50 (M.op x X3) x X3 X4 X5 X6
       have i₂ := eq56 X0 (M.op x X3) X1
       grind)
    | (have i₁ := eq50 (M.op X0 X0) X1 x X4 X5 X6
       have i₂ := eq56 X0 X1 (M.op X1 x)
       grind)
    | exact superpose eq56 eq50
    | exact resolve eq50 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq744 : ∀ X0 X1 X2 : G, (k X1 (σ (M.op X2 X2))) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X1 (M.op X2 X2)
       have i₂ := eq304 X0 X2 (τ X1)
       grind)
    | exact superpose eq304 eq34
    | exact resolve eq34 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq821 : ∀ X0 X1 X2 X4 X5 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op (M.op (M.op X0 (M.op x y)) y) X4)) X5) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq51 (M.op x X4) x X4 X1 X2 X5
       have i₂ := eq53 (M.op x X4) X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq951 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq345 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq345
    | exact resolve eq345 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq1266 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X0
       have i₂ := eq57 (σ X0) X1
       grind)
    | (have i₁ := eq84 X0 X0
       have i₂ := eq57 X0 (σ X0)
       grind)
    | exact superpose eq57 eq84
    | exact resolve eq84 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1310 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1266 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266
  have eq11150 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1310 X0 (τ X1)
       grind)
    | exact superpose eq1310 eq34
    | (have j1 := eq1310 X0 (τ X1)
       grind)
    | exact resolve eq34 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq11153 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq144
       have i₂ := eq1310 X0 sF0
       grind)
    | exact superpose eq1310 eq144
    | (have j1 := eq1310 X0 (M.op x y)
       grind)
    | exact resolve eq144 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11167 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1310 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq11171 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq11153
    | (have j0 := eq11153 X0
       grind)
    | exact resolve eq11153 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11153
  have eq11174 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq11150 X0 X1
       have j1 := eq78 X0 (σ (τ X1)) X1
       grind)
    | (have r₁ := eq11150 X0 X1
       have r₂ := eq78 X0 (k X1 (σ (τ X1))) x
       grind)
    | (have r₁ := eq11150 X0 X1
       have r₂ := eq78 X0 (σ (τ X1)) x
       grind)
    | exact resolve eq11150 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11150
  have eq11191 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq11171 X0
       have j1 := eq78 X0 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq11171 X0
       have r₂ := eq78 X0 (σ (M.op x y)) x
       grind)
    | (have r₁ := eq11171 X0
       have r₂ := eq78 X0 (k (σ (M.op x y)) (σ (M.op x y))) x
       grind)
    | exact resolve eq11171 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq11171
  have eq11194 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11174 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq11174
    | exact resolve eq11174 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11174
  have eq11210 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq11191 x
       have i₂ := eq53 x X0
       grind)
    | exact superpose eq53 eq11191
    | exact resolve eq11191 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq11211 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11191 x
       have i₂ := eq54 x X0
       grind)
    | exact superpose eq54 eq11191
    | exact resolve eq11191 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq11213 : ∀ X0 X1 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11191 x
       have i₂ := eq56 X0 x X1
       grind)
    | (have i₁ := eq11191 (M.op X0 X0)
       have i₂ := eq56 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq56 eq11191
    | exact resolve eq11191 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq11396 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq11191 eq167
    | exact resolve eq167 eq11191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq11849 : ∀ X1 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (k X1 X1) := by
    intro X1
    first
    | (have i₁ := eq11194 x X1
       have i₂ := eq11191 x
       grind)
    | exact superpose eq11191 eq11194
    | exact resolve eq11194 eq11191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11191
  have eq11852 : ∀ X0 X2 : G, (k X2 X2) = (k X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq11194 x X0
       have i₂ := eq11194 x X2
       grind)
    | exact superpose eq11194 eq11194
    | exact resolve eq11194 eq11194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11892 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11194 X1 (σ (M.op x x))
       have i₂ := eq744 X0 (σ (M.op x x)) x
       grind)
    | exact superpose eq744 eq11194
    | exact resolve eq11194 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq12074 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq144
       have i₂ := eq11194 X0 sF0
       grind)
    | exact superpose eq11194 eq144
    | exact resolve eq144 eq11194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12680 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11849 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq11849
    | exact resolve eq11849 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12682 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11849 (τ X0)
       have i₂ := eq951 X0 X0
       grind)
    | exact superpose eq951 eq11849
    | exact resolve eq11849 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq27716 : ∀ X1 X2 X4 X5 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op (k (σ (M.op x y)) (σ (M.op x y))) X4)) X5) := by
    intro X1 X2 X4 X5
    first
    | exact superpose eq11210 eq821
    | exact resolve eq821 eq11210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq28420 : ∀ X0 X4 X5 X6 X7 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op (M.op X5 X5) X6) X7) := by
    intro X0 X4 X5 X6 X7
    first
    | (have i₁ := eq616 X0 x x (M.op X5 X6) X5 X6
       have i₂ := eq27716 (M.op X5 X6) x X4 X5
       grind)
    | exact superpose eq27716 eq616
    | exact resolve eq616 eq27716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq27716
  have eq28474 : ∀ X0 X4 X7 : G, (M.op (M.op X0 X0) X4) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) X7) := by
    intro X0 X4 X7
    first
    | (have i₁ := eq28420 X0 X4 x x X7
       have i₂ := eq11213 x x
       grind)
    | exact superpose eq11213 eq28420
    | exact resolve eq28420 eq11213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28420
  have eq28638 : ∀ X7 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) X7) := by
    intro X7
    first
    | (have i₁ := eq28474 x x X7
       have i₂ := eq11213 x x
       grind)
    | exact superpose eq11213 eq28474
    | exact resolve eq28474 eq11213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11213 eq28474
  have eq104065 : ∀ X0 X1 : G, (σ X1) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11167 X0 X1
       have i₂ := eq12680 X1
       grind)
    | exact superpose eq12680 eq11167
    | (have j0 := eq11167 X0 X1
       grind)
    | exact resolve eq11167 eq12680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11167
  have eq104074 : ∀ X0 X1 : G, (k (σ (M.op x y)) (σ (M.op x y))) ≠ X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq104065 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq104065
    | (have r₁ := eq104065 X0 (τ (k (σ (M.op x y)) (σ (M.op x y))))
       have r₂ := eq15 (k (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq104065 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104065
  have eq104175 : ∀ X0 X1 X2 : G, (k X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104074 X0 X1
       have i₂ := eq11849 sF1
       grind)
    | exact superpose eq11849 eq104074
    | (have j0 := eq104074 X1 X2
       grind)
    | (have r₁ := eq104074 (k X1 X1) X1
       have r₂ := eq11849 X1
       grind)
    | (have r₁ := eq104074 (k (σ (M.op x y)) (σ (M.op x y))) X1
       have r₂ := eq11849 (σ (M.op x y))
       grind)
    | exact resolve eq104074 eq11849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104074
  have eq117361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq117368 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq117361
    | exact resolve eq117361 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117361
  have eq117379 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq117368
       have r₂ := eq27
       grind)
    | exact resolve eq117368 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117368
  have eq117438 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq117379 eq11396
    | exact resolve eq11396 eq117379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117379
  have eq117526 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq117438
    | exact resolve eq117438 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117438
  have eq117565 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq104175 x (σ x) (σ x)
       grind)
    | (have r₁ := eq117526
       have r₂ := eq104175 (M.op x y) y x
       grind)
    | exact resolve eq117526 eq104175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117526
  have eq117632 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq117565 eq11396
    | exact resolve eq11396 eq117565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11396 eq117565
  have eq117720 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq28 eq117632
    | exact resolve eq117632 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117632
  have eq117759 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq104175 x y y
       grind)
    | (have r₁ := eq117720
       have r₂ := eq104175 (M.op x y) x x
       grind)
    | exact resolve eq117720 eq104175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117720
  have eq117769 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq117759
       have i₂ := eq57 y X0
       grind)
    | (have i₁ := eq117759
       have i₂ := eq57 X0 y
       grind)
    | exact superpose eq57 eq117759
    | exact resolve eq117759 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117828 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12074 y
       have i₂ := eq117759
       grind)
    | exact superpose eq117759 eq12074
    | exact resolve eq12074 eq117759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117759
  have eq117915 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq117828
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq117828
    | exact resolve eq117828 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117828
  have eq117967 : ∀ X0 X1 : G, x ≠ x ∨ x = (k X0 x) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq117769 X0
       grind)
    | exact superpose eq117769 eq13
    | (have j1 := eq117769 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq117769 X0
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq117769 y
       grind)
    | exact resolve eq13 eq117769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118022 : ∀ X0 X1 : G, (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq11892 x X0
       have i₂ := eq117769 X1
       grind)
    | exact superpose eq117769 eq11892
    | (have j1 := eq117769 X1
       grind)
    | exact resolve eq11892 eq117769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11892 eq117769
  have eq118084 : ∀ X0 X1 : G, x = (k X0 x) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have j0 := eq117967 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117967
  have eq118112 : ∀ X0 X1 : G, (M.op X1 X1) = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq118022 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq118022
    | (have j0 := eq118022 X0 X1
       grind)
    | exact resolve eq118022 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118022
  have eq118468 : (σ y) = (τ (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq117915 eq12682
    | exact resolve eq12682 eq117915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12682 eq117915
  have eq118534 : x = (M.op x x) ∨ y = (σ y) := by
    first
    | exact superpose eq29 eq118468
    | exact resolve eq118468 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118468
  have eq118548 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq118534
       have i₂ := eq57 x X0
       grind)
    | (have i₁ := eq118534
       have i₂ := eq57 X0 x
       grind)
    | exact superpose eq57 eq118534
    | exact resolve eq118534 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq118607 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq12074 x
       have i₂ := eq118534
       grind)
    | exact superpose eq118534 eq12074
    | exact resolve eq12074 eq118534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12074 eq118534
  have eq118694 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq118607
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq118607
    | exact resolve eq118607 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118607
  have eq119166 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq11210 sF0
       have i₂ := eq118548 sF0
       grind)
    | exact superpose eq118548 eq11210
    | exact resolve eq11210 eq118548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118548
  have eq119327 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq119166
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119166
    | exact resolve eq119166 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119166
  have eq119989 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq118694 eq28638
    | exact resolve eq28638 eq118694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123887 : (M.op x y) = (σ x) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq119327 eq118694
    | exact resolve eq118694 eq119327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118694
  have eq123899 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq119327 eq12680
    | exact resolve eq12680 eq119327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12680 eq119327
  have eq123959 : (M.op x y) = (σ x) ∨ y = (σ y) := by grind
  clear eq123887
  have eq123976 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq123899
    | exact resolve eq123899 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123899
  have eq126141 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq26 eq119989
    | (have j0 := eq119989 (σ y)
       grind)
    | exact resolve eq119989 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119989
  have eq126511 : (σ (M.op x y)) ≠ (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq126141 eq27
    | exact resolve eq27 eq126141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126141
  have eq126535 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq123959 eq126511
    | exact resolve eq126511 eq123959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123959 eq126511
  have eq126536 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by grind
  clear eq126535
  have eq126537 : y = (σ y) := by
    first
    | (have r₁ := eq126536
       have r₂ := eq123976
       grind)
    | exact resolve eq126536 eq123976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123976 eq126536
  have eq126541 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq126537 eq26
    | exact resolve eq26 eq126537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126542 : y = (τ y) := by
    first
    | exact superpose eq126537 eq29
    | exact resolve eq29 eq126537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq130246 : ∀ X0 X1 : G, x = (k X0 X0) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq118084 x X1
       have i₂ := eq11852 X0 x
       grind)
    | (have i₁ := eq118084 x X1
       have i₂ := eq11852 x X0
       grind)
    | exact superpose eq11852 eq118084
    | (have j0 := eq118084 X0 X1
       grind)
    | exact resolve eq118084 eq11852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11852 eq118084
  have eq136294 : ∀ X0 X2 : G, (σ x) = (M.op X2 X2) ∨ y = (k X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq118112 X2 x
       have i₂ := eq11194 x X0
       grind)
    | exact superpose eq11194 eq118112
    | (have j0 := eq118112 X2 x
       grind)
    | exact resolve eq118112 eq11194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11194 eq118112
  have eq139275 : ∀ X0 X1 : G, x = (M.op x X0) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq28638 x
       have i₂ := eq130246 sF1 X1
       grind)
    | exact superpose eq130246 eq28638
    | (have j1 := eq130246 X0 X1
       grind)
    | exact resolve eq28638 eq130246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28638 eq130246
  have eq144360 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq11211 sF4
       have i₂ := eq136294 X0 sF4
       grind)
    | exact superpose eq136294 eq11211
    | (have j1 := eq136294 X0 x
       grind)
    | exact resolve eq11211 eq136294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11211 eq136294
  have eq144515 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq26 eq144360
    | (have j0 := eq144360 X0
       grind)
    | exact resolve eq144360 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq144360
  have eq150188 : ∀ X0 : G, (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq11210 x
       have i₂ := eq139275 sF0 x
       grind)
    | exact superpose eq139275 eq11210
    | (have j1 := eq139275 X0 X0
       grind)
    | exact resolve eq11210 eq139275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11210 eq139275
  have eq150220 : ∀ X0 : G, (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq150188 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq150188
    | (have j0 := eq150188 X0
       grind)
    | exact resolve eq150188 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150188
  have eq165651 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (k X0 X0) ∨ y = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq144515 X0
       have i₂ := eq11849 sF1
       grind)
    | exact superpose eq11849 eq144515
    | (have j0 := eq144515 X1
       grind)
    | exact resolve eq144515 eq11849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144515
  have eq178027 : ∀ X0 X1 : G, (M.op x y) = (k X0 X0) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq150220 X0
       have i₂ := eq11849 sF1
       grind)
    | exact superpose eq11849 eq150220
    | (have j0 := eq150220 X1
       grind)
    | exact resolve eq150220 eq11849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11849 eq150220
  have eq218081 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq144
       have i₂ := eq178027 sF0 x
       grind)
    | exact superpose eq178027 eq144
    | (have j1 := eq178027 X0 X0
       grind)
    | exact resolve eq144 eq178027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq178027
  have eq218183 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq20 eq218081
    | (have j0 := eq218081 X0
       grind)
    | exact resolve eq218081 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218081
  have eq260161 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k X0 X0) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | exact superpose eq218183 eq165651
    | (have j0 := eq165651 X0 X0
       have j1 := eq218183 X1
       grind)
    | exact resolve eq165651 eq218183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165651 eq218183
  have eq260190 : ∀ X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X1 X1) = y := by
    intro X1
    first
    | (have j0 := eq260161 x X1
       have j1 := eq104175 x y X1
       grind)
    | (have r₁ := eq260161 x X1
       have r₂ := eq104175 x y x
       grind)
    | exact resolve eq260161 eq104175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104175 eq260161
  have eq260228 : ∀ X1 : G, (M.op X1 X1) = y := by
    intro X1
    first
    | (have j0 := eq260190 X1
       grind)
    | (have r₁ := eq260190 X1
       have r₂ := eq27
       grind)
    | exact resolve eq260190 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260190
  have eq260446 : ∀ X1 : G, (M.op X1 y) = (k y X1) ∨ (M.op X1 X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq305 X1 x
       have i₂ := eq260228 X1
       grind)
    | exact superpose eq260228 eq305
    | (have j0 := eq305 X1 X1
       grind)
    | exact resolve eq305 eq260228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq261176 : ∀ X1 : G, (M.op X1 y) = (k y X1) ∨ y = X1 := by
    intro X1
    first
    | (have i₁ := eq260446 X1
       have i₂ := eq260228 X1
       grind)
    | exact superpose eq260228 eq260446
    | (have j0 := eq260446 X1
       grind)
    | exact resolve eq260446 eq260228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260446
  have eq268697 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq103
       have i₂ := eq261176 x
       grind)
    | exact superpose eq261176 eq103
    | (have j1 := eq261176 x
       grind)
    | exact resolve eq103 eq261176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq268743 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y := by
    first
    | exact superpose eq126537 eq268697
    | exact resolve eq268697 eq126537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268697
  have eq268800 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq268743
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq268743
    | exact resolve eq268743 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268743
  have eq268841 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y := by
    first
    | exact superpose eq20 eq268800
    | exact resolve eq268800 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268800
  have eq268881 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq268841 eq261176
    | (have j0 := eq261176 (σ x)
       grind)
    | exact resolve eq261176 eq268841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261176 eq268841
  have eq268895 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq126541 eq268881
    | exact resolve eq268881 eq126541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268881
  have eq268904 : y = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq268895
       have r₂ := eq27
       grind)
    | exact resolve eq268895 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268895
  have eq268912 : x = (τ y) ∨ x = y := by
    first
    | exact superpose eq268904 eq28
    | exact resolve eq28 eq268904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq268904
  have eq269055 : x = y ∨ x = y := by
    first
    | (have i₁ := eq268912
       have i₂ := eq126542
       grind)
    | exact superpose eq126542 eq268912
    | exact resolve eq268912 eq126542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126542 eq268912
  have eq269056 : x = y := by grind
  clear eq269055
  have eq269179 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq269056
       grind)
    | exact superpose eq269056 eq18
    | exact resolve eq18 eq269056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269180 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq269056
       grind)
    | exact superpose eq269056 eq24
    | exact resolve eq24 eq269056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq269565 : y = (σ x) := by
    first
    | exact superpose eq126537 eq269180
    | exact resolve eq269180 eq126537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126537 eq269180
  have eq269566 : y = (M.op x y) := by
    first
    | (have i₁ := eq269179
       have i₂ := eq260228 x
       grind)
    | exact superpose eq260228 eq269179
    | exact resolve eq269179 eq260228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260228 eq269179
  have eq269688 : y = (σ x) := by
    first
    | (have i₁ := eq269565
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq269565
    | exact resolve eq269565 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269565
  have eq269689 : x = (M.op x y) := by
    first
    | (have i₁ := eq269566
       have i₂ := eq269056
       grind)
    | exact superpose eq269056 eq269566
    | exact resolve eq269566 eq269056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269566
  have eq269753 : x = (σ x) := by
    first
    | (have i₁ := eq269688
       have i₂ := eq269056
       grind)
    | exact superpose eq269056 eq269688
    | exact resolve eq269688 eq269056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269056 eq269688
  have eq269852 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq269689 eq20
    | exact resolve eq20 eq269689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq270032 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq269852
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq269852
    | exact resolve eq269852 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq269852
  have eq270345 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq269753 eq126541
    | exact resolve eq126541 eq269753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126541
  have eq270363 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq270345
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq270345
    | exact resolve eq270345 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq270345
  have eq270418 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq269689 eq270363
    | exact resolve eq270363 eq269689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269689 eq270363
  have eq270587 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq269753 eq270032
    | exact resolve eq270032 eq269753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269753 eq270032
  have eq270589 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq270418 eq27
    | exact resolve eq27 eq270418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq270418
  have eq271371 : False := by grind
  exact eq271371

/-- `Equation3912`: `x ◇ x = (y ◇ (z ◇ w)) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyy_pyx_pxy_Equation3912 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X3)) X3) := by
    intro X0 X1 X2 X3
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq51 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (M.op (M.op X4 (M.op X5 X6)) X6) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq14 x X4 X5 X6
       have i₂ := eq14 x X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X3) = (M.op (M.op X4 (M.op (M.op X0 (M.op X1 X2)) X2)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X3 X4 X5 X5
       have i₂ := eq14 X5 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op x y)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X5 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X5) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq14 X1 (M.op x (M.op x (M.op x X5))) x X5
       have i₂ := eq14 X0 x x (M.op x X5)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq58 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq13
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq58 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq58 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq37
  have eq105 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
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
  clear eq45
  have eq123 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq113
    | exact resolve eq113 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq124 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq123
    | exact resolve eq123 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq145 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq168 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq145 eq16
    | exact resolve eq16 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq57 X0 X1 x
       grind)
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq57 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq57 eq13
    | (have r₁ := eq13 X0 (M.op (M.op X0 X0) x)
       have r₂ := eq57 X0 (M.op (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq57 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq294 X0 X1 X2
       grind)
    | (have r₁ := eq294 X0 X1 X2
       have r₂ := eq58 X0 X1
       grind)
    | (have r₁ := eq294 X1 X0 X2
       have r₂ := eq58 X0 X1
       grind)
    | exact resolve eq294 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq345 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq616 : ∀ X0 X1 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 X6)) X6) = (M.op (M.op (M.op X0 X0) X1) X3) := by
    intro X0 X1 X3 X4 X5 X6
    first
    | (have i₁ := eq51 (M.op x X3) x X3 X4 X5 X6
       have i₂ := eq57 X0 (M.op x X3) X1
       grind)
    | (have i₁ := eq51 (M.op X0 X0) X1 x X4 X5 X6
       have i₂ := eq57 X0 X1 (M.op X1 x)
       grind)
    | exact superpose eq57 eq51
    | exact resolve eq51 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq728 : ∀ X0 X1 X2 X4 : G, (M.op X2 X2) = (M.op (k X0 (M.op X1 X1)) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq57 x X2 X4
       have i₂ := eq305 x X1 X0
       grind)
    | exact superpose eq305 eq57
    | exact resolve eq57 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 X1 X2 : G, (k X1 (σ (M.op X2 X2))) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 X1 (M.op X2 X2)
       have i₂ := eq305 X0 X2 (τ X1)
       grind)
    | exact superpose eq305 eq35
    | exact resolve eq35 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq823 : ∀ X0 X1 X2 X4 X5 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op (M.op (M.op X0 (M.op x y)) y) X4)) X5) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq52 (M.op x X4) x X4 X1 X2 X5
       have i₂ := eq54 (M.op x X4) X0
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq953 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq345 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq345
    | exact resolve eq345 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq1187 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 X0
       have i₂ := eq58 (σ X0) X1
       grind)
    | (have i₁ := eq105 X0 X0
       have i₂ := eq58 X0 (σ X0)
       grind)
    | exact superpose eq58 eq105
    | exact resolve eq105 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1191 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq105
  have eq1226 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1191 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq1230 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1187 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1239 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1226 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq1226
    | (have j0 := eq1226 X0
       grind)
    | exact resolve eq1226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq11210 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1230 X0 (τ X1)
       grind)
    | exact superpose eq1230 eq35
    | (have j1 := eq1230 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11213 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq145
       have i₂ := eq1230 X0 sF0
       grind)
    | exact superpose eq1230 eq145
    | (have j1 := eq1230 X0 (M.op x y)
       grind)
    | exact resolve eq145 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11227 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1230 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq11231 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq11213
    | (have j0 := eq11213 X0
       grind)
    | exact resolve eq11213 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11213
  have eq11234 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq11210 X0 X1
       have j1 := eq79 X0 (σ (τ X1)) X1
       grind)
    | (have r₁ := eq11210 X0 X1
       have r₂ := eq79 X0 (k X1 (σ (τ X1))) x
       grind)
    | (have r₁ := eq11210 X0 X1
       have r₂ := eq79 X0 (σ (τ X1)) x
       grind)
    | exact resolve eq11210 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11210
  have eq11251 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq11231 X0
       have j1 := eq79 X0 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq11231 X0
       have r₂ := eq79 X0 (σ (M.op x y)) x
       grind)
    | (have r₁ := eq11231 X0
       have r₂ := eq79 X0 (k (σ (M.op x y)) (σ (M.op x y))) x
       grind)
    | exact resolve eq11231 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq11231
  have eq11254 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11234 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq11234
    | exact resolve eq11234 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11234
  have eq11270 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq11251 x
       have i₂ := eq54 x X0
       grind)
    | exact superpose eq54 eq11251
    | exact resolve eq11251 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq11271 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11251 x
       have i₂ := eq55 x X0
       grind)
    | exact superpose eq55 eq11251
    | exact resolve eq11251 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq11273 : ∀ X0 X1 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11251 x
       have i₂ := eq57 X0 x X1
       grind)
    | (have i₁ := eq11251 (M.op X0 X0)
       have i₂ := eq57 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq57 eq11251
    | exact resolve eq11251 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq11456 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq11251 eq168
    | exact resolve eq168 eq11251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq11909 : ∀ X1 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (k X1 X1) := by
    intro X1
    first
    | (have i₁ := eq11254 x X1
       have i₂ := eq11251 x
       grind)
    | exact superpose eq11251 eq11254
    | exact resolve eq11254 eq11251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11952 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11254 X1 (σ (M.op x x))
       have i₂ := eq746 X0 (σ (M.op x x)) x
       grind)
    | exact superpose eq746 eq11254
    | exact resolve eq11254 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq12134 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq145
       have i₂ := eq11254 X0 sF0
       grind)
    | exact superpose eq11254 eq145
    | exact resolve eq145 eq11254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12750 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11909 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq11909
    | exact resolve eq11909 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12752 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11909 (τ X0)
       have i₂ := eq953 X0 X0
       grind)
    | exact superpose eq953 eq11909
    | exact resolve eq11909 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq27784 : ∀ X1 X2 X4 X5 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op (k (σ (M.op x y)) (σ (M.op x y))) X4)) X5) := by
    intro X1 X2 X4 X5
    first
    | exact superpose eq11270 eq823
    | exact resolve eq823 eq11270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq28488 : ∀ X0 X4 X5 X6 X7 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op (M.op X5 X5) X6) X7) := by
    intro X0 X4 X5 X6 X7
    first
    | (have i₁ := eq616 X0 x x (M.op X5 X6) X5 X6
       have i₂ := eq27784 (M.op X5 X6) x X4 X5
       grind)
    | exact superpose eq27784 eq616
    | exact resolve eq616 eq27784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq27784
  have eq28542 : ∀ X0 X4 X7 : G, (M.op (M.op X0 X0) X4) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) X7) := by
    intro X0 X4 X7
    first
    | (have i₁ := eq28488 X0 X4 x x X7
       have i₂ := eq11273 x x
       grind)
    | exact superpose eq11273 eq28488
    | exact resolve eq28488 eq11273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28488
  have eq28706 : ∀ X7 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) X7) := by
    intro X7
    first
    | (have i₁ := eq28542 x x X7
       have i₂ := eq11273 x x
       grind)
    | exact superpose eq11273 eq28542
    | exact resolve eq28542 eq11273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11273 eq28542
  have eq67842 : ∀ X0 : G, (M.op (σ X0) (k (σ (M.op x y)) (σ (M.op x y)))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1239 X0
       have i₂ := eq12750 X0
       grind)
    | exact superpose eq12750 eq1239
    | (have j0 := eq1239 X0
       grind)
    | exact resolve eq1239 eq12750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq67843 : ∀ X0 : G, (σ X0) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ X0) (k (σ (M.op x y)) (σ (M.op x y)))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq67842 X0
       have i₂ := eq12750 X0
       grind)
    | exact superpose eq12750 eq67842
    | (have j0 := eq67842 X0
       grind)
    | exact resolve eq67842 eq12750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67842
  have eq67844 : ∀ X0 : G, (σ X0) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ X0) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ X0) (k (σ (M.op x y)) (σ (M.op x y)))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq67843 X0
       have i₂ := eq11251 (σ X0)
       grind)
    | exact superpose eq11251 eq67843
    | (have j0 := eq67843 X0
       grind)
    | exact resolve eq67843 eq11251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67843
  have eq67845 : ∀ X0 : G, (M.op (σ X0) (k (σ (M.op x y)) (σ (M.op x y)))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq67844 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67844
  have eq67949 : ∀ X0 : G, (M.op (σ (τ X0)) (k (σ (M.op x y)) (σ (M.op x y)))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq39 X0 (k (τ X0) (τ X0))
       have i₂ := eq67845 (τ X0)
       grind)
    | exact superpose eq67845 eq39
    | (have j1 := eq67845 (τ X0)
       grind)
    | exact resolve eq39 eq67845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq67845
  have eq67983 : ∀ X0 : G, (M.op (σ (τ X0)) (k (σ (M.op x y)) (σ (M.op x y)))) = (k (k X0 (σ (τ X0))) X0) ∨ (σ (τ X0)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq67949 X0
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq67949
    | (have j0 := eq67949 X0
       grind)
    | exact resolve eq67949 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq67949
  have eq68026 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (τ X0)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq67983 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq67983
    | (have j0 := eq67983 X0
       grind)
    | exact resolve eq67983 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67983
  have eq68052 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = X0 ∨ (k (k X0 X0) X0) = (M.op X0 (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq68026 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq68026
    | (have j0 := eq68026 X0
       grind)
    | exact resolve eq68026 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68026
  have eq105706 : ∀ X0 X1 : G, (σ X1) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11227 X0 X1
       have i₂ := eq12750 X1
       grind)
    | exact superpose eq12750 eq11227
    | (have j0 := eq11227 X0 X1
       grind)
    | exact resolve eq11227 eq12750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11227
  have eq105716 : ∀ X0 X1 : G, (k (σ (M.op x y)) (σ (M.op x y))) ≠ X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq105706 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq105706
    | (have r₁ := eq105706 X0 (τ (k (σ (M.op x y)) (σ (M.op x y))))
       have r₂ := eq15 (k (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq105706 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105706
  have eq105818 : ∀ X0 X1 X2 : G, (k X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105716 X0 X1
       have i₂ := eq11909 sF1
       grind)
    | exact superpose eq11909 eq105716
    | (have j0 := eq105716 X1 X2
       grind)
    | (have r₁ := eq105716 (k X1 X1) X1
       have r₂ := eq11909 X1
       grind)
    | (have r₁ := eq105716 (k (σ (M.op x y)) (σ (M.op x y))) X1
       have r₂ := eq11909 (σ (M.op x y))
       grind)
    | exact resolve eq105716 eq11909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105716
  have eq120329 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq124 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq120336 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq120329
    | exact resolve eq120329 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120329
  have eq120347 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq120336
       have r₂ := eq28
       grind)
    | exact resolve eq120336 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120336
  have eq120404 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq120347 eq11456
    | exact resolve eq11456 eq120347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120347
  have eq120494 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq120404
    | exact resolve eq120404 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120404
  have eq120533 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq105818 x (σ x) (σ y)
       grind)
    | (have r₁ := eq120494
       have r₂ := eq105818 (M.op x y) y x
       grind)
    | exact resolve eq120494 eq105818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120494
  have eq120600 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq120533 eq11456
    | exact resolve eq11456 eq120533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11456 eq120533
  have eq120689 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq120600
    | exact resolve eq120600 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120600
  have eq120728 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq105818 x y y
       grind)
    | (have r₁ := eq120689
       have r₂ := eq105818 (M.op x y) x x
       grind)
    | exact resolve eq120689 eq105818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120689
  have eq120738 : ∀ X0 : G, (M.op X0 X0) = y ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq120728
       have i₂ := eq58 y x
       grind)
    | (have i₁ := eq120728
       have i₂ := eq58 X0 y
       grind)
    | exact superpose eq58 eq120728
    | exact resolve eq120728 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120743 : ∀ X0 : G, x = (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq58 y X0
       have i₂ := eq120728
       grind)
    | exact superpose eq120728 eq58
    | exact resolve eq58 eq120728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120795 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12134 y
       have i₂ := eq120728
       grind)
    | exact superpose eq120728 eq12134
    | exact resolve eq12134 eq120728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120728
  have eq120884 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq120795
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq120795
    | exact resolve eq120795 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120795
  have eq121479 : ∀ X0 X1 X2 : G, (M.op X0 X0) = y ∨ x = (M.op (k X1 (M.op X2 X2)) (k X1 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq728 X1 X2 X0 (k X1 (M.op X2 X2))
       have i₂ := eq120738 (k X1 (M.op X2 X2))
       grind)
    | exact superpose eq120738 eq728
    | (have j1 := eq120738 X0
       grind)
    | exact resolve eq728 eq120738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728 eq120738
  have eq121487 : ∀ X0 : G, x = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq121479 X0 x x
       have i₂ := eq11251 (k x (M.op x x))
       grind)
    | exact superpose eq11251 eq121479
    | (have j0 := eq121479 X0 x x
       grind)
    | exact resolve eq121479 eq11251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121479
  have eq122260 : ∀ X0 X1 : G, (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq11952 y X0
       have i₂ := eq120743 X1
       grind)
    | exact superpose eq120743 eq11952
    | (have j1 := eq120743 X1
       grind)
    | exact resolve eq11952 eq120743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11952 eq120743
  have eq122350 : ∀ X0 X1 : G, (M.op X1 X1) = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq122260 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq122260
    | (have j0 := eq122260 X0 X1
       grind)
    | exact resolve eq122260 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122260
  have eq122728 : (σ y) = (τ (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq120884 eq12752
    | exact resolve eq12752 eq120884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12752 eq120884
  have eq122795 : x = (M.op y y) ∨ y = (σ y) := by
    first
    | exact superpose eq30 eq122728
    | exact resolve eq122728 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122728
  have eq122809 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq122795
       have i₂ := eq58 y X0
       grind)
    | (have i₁ := eq122795
       have i₂ := eq58 X0 y
       grind)
    | exact superpose eq58 eq122795
    | exact resolve eq122795 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq122868 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq12134 y
       have i₂ := eq122795
       grind)
    | exact superpose eq122795 eq12134
    | exact resolve eq12134 eq122795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12134 eq122795
  have eq122955 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq122868
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq122868
    | exact resolve eq122868 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122868
  have eq123431 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq11270 sF0
       have i₂ := eq122809 sF0
       grind)
    | exact superpose eq122809 eq11270
    | exact resolve eq11270 eq122809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122809
  have eq123593 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq123431
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq123431
    | exact resolve eq123431 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123431
  have eq123986 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq122955 eq28706
    | exact resolve eq28706 eq122955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127974 : (M.op x y) = (σ x) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq123593 eq122955
    | exact resolve eq122955 eq123593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122955
  have eq127986 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq123593 eq12750
    | exact resolve eq12750 eq123593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12750 eq123593
  have eq128047 : (M.op x y) = (σ x) ∨ y = (σ y) := by grind
  clear eq127974
  have eq128064 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq21 eq127986
    | exact resolve eq127986 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127986
  have eq130010 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq27 eq123986
    | (have j0 := eq123986 (σ y)
       grind)
    | exact resolve eq123986 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123986
  have eq130382 : (σ (M.op x y)) ≠ (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq130010 eq28
    | exact resolve eq28 eq130010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130010
  have eq130406 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq128047 eq130382
    | exact resolve eq130382 eq128047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128047 eq130382
  have eq130407 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by grind
  clear eq130406
  have eq130408 : y = (σ y) := by
    first
    | (have r₁ := eq130407
       have r₂ := eq128064
       grind)
    | exact resolve eq130407 eq128064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128064 eq130407
  have eq130409 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq130408 eq27
    | exact resolve eq27 eq130408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130410 : y = (τ y) := by
    first
    | exact superpose eq130408 eq30
    | exact resolve eq30 eq130408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq135787 : ∀ X0 X1 : G, x = (M.op x X0) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | exact superpose eq121487 eq28706
    | (have j1 := eq121487 X1
       grind)
    | exact resolve eq28706 eq121487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28706 eq121487
  have eq144528 : ∀ X0 X2 : G, (σ x) = (M.op X2 X2) ∨ y = (k X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq122350 X2 x
       have i₂ := eq11254 x X0
       grind)
    | exact superpose eq11254 eq122350
    | (have j0 := eq122350 X2 x
       grind)
    | exact resolve eq122350 eq11254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122350
  have eq150173 : ∀ X0 : G, (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq11270 x
       have i₂ := eq135787 sF0 x
       grind)
    | exact superpose eq135787 eq11270
    | (have j1 := eq135787 X0 X0
       grind)
    | exact resolve eq11270 eq135787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11270 eq135787
  have eq150204 : ∀ X0 : G, (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq150173 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq150173
    | (have j0 := eq150173 X0
       grind)
    | exact resolve eq150173 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150173
  have eq158895 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq11271 sF4
       have i₂ := eq144528 X0 sF4
       grind)
    | exact superpose eq144528 eq11271
    | (have j1 := eq144528 X0 x
       grind)
    | exact resolve eq11271 eq144528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11271 eq144528
  have eq159056 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq27 eq158895
    | (have j0 := eq158895 X0
       grind)
    | exact resolve eq158895 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158895
  have eq164865 : ∀ X0 X1 : G, (M.op x y) = (k X0 X0) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq150204 X0
       have i₂ := eq11909 sF1
       grind)
    | exact superpose eq11909 eq150204
    | (have j0 := eq150204 X1
       grind)
    | exact resolve eq150204 eq11909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150204
  have eq191079 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (k X0 X0) ∨ y = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq159056 X0
       have i₂ := eq11909 sF1
       grind)
    | exact superpose eq11909 eq159056
    | (have j0 := eq159056 X1
       grind)
    | exact resolve eq159056 eq11909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11909 eq159056
  have eq208925 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq145
       have i₂ := eq164865 sF0 x
       grind)
    | exact superpose eq164865 eq145
    | (have j1 := eq164865 X0 X0
       grind)
    | exact resolve eq145 eq164865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq164865
  have eq209025 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq21 eq208925
    | (have j0 := eq208925 X0
       grind)
    | exact resolve eq208925 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208925
  have eq254302 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k X0 X0) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | exact superpose eq209025 eq191079
    | (have j0 := eq191079 X0 X0
       have j1 := eq209025 X1
       grind)
    | exact resolve eq191079 eq209025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191079 eq209025
  have eq254323 : ∀ X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X1 X1) = y := by
    intro X1
    first
    | (have j0 := eq254302 x X1
       have j1 := eq105818 x y X1
       grind)
    | (have r₁ := eq254302 x X1
       have r₂ := eq105818 x y x
       grind)
    | exact resolve eq254302 eq105818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105818 eq254302
  have eq254364 : ∀ X1 : G, (M.op X1 X1) = y := by
    intro X1
    first
    | (have j0 := eq254323 X1
       grind)
    | (have r₁ := eq254323 X1
       have r₂ := eq28
       grind)
    | exact resolve eq254323 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254323
  have eq254415 : y = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq254364 x
       have i₂ := eq11251 x
       grind)
    | exact superpose eq11251 eq254364
    | exact resolve eq254364 eq11251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11251
  have eq254418 : ∀ X0 : G, y = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq254364 x
       have i₂ := eq11254 x X0
       grind)
    | exact superpose eq11254 eq254364
    | exact resolve eq254364 eq11254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11254
  have eq262544 : ∀ X0 : G, y = X0 ∨ (k (k X0 X0) X0) = (M.op X0 (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq254415 eq68052
    | (have j0 := eq68052 X0
       grind)
    | exact resolve eq68052 eq254415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68052
  have eq262545 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 y) ∨ y = X0 := by
    intro X0
    first
    | exact superpose eq254415 eq262544
    | (have j0 := eq262544 X0
       grind)
    | exact resolve eq262544 eq254415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254415 eq262544
  have eq262546 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq262545 X0
       have i₂ := eq254418 X0
       grind)
    | exact superpose eq254418 eq262545
    | (have j0 := eq262545 X0
       grind)
    | exact resolve eq262545 eq254418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254418 eq262545
  have eq262642 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq92
       have i₂ := eq262546 x
       grind)
    | exact superpose eq262546 eq92
    | (have j1 := eq262546 x
       grind)
    | exact resolve eq92 eq262546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq262690 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y := by
    first
    | exact superpose eq130408 eq262642
    | exact resolve eq262642 eq130408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262642
  have eq262746 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq262690
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq262690
    | exact resolve eq262690 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262690
  have eq262787 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq262746
    | exact resolve eq262746 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262746
  have eq262828 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq262787 eq262546
    | (have j0 := eq262546 (σ x)
       grind)
    | exact resolve eq262546 eq262787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262546 eq262787
  have eq262842 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq130409 eq262828
    | exact resolve eq262828 eq130409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130409 eq262828
  have eq262851 : y = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq262842
       have r₂ := eq28
       grind)
    | exact resolve eq262842 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262842
  have eq262859 : x = (τ y) ∨ x = y := by
    first
    | exact superpose eq262851 eq29
    | exact resolve eq29 eq262851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq262851
  have eq263006 : x = y ∨ x = y := by
    first
    | (have i₁ := eq262859
       have i₂ := eq130410
       grind)
    | exact superpose eq130410 eq262859
    | exact resolve eq262859 eq130410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130410 eq262859
  have eq263007 : x = y := by grind
  clear eq263006
  have eq263150 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq263007
       grind)
    | exact superpose eq263007 eq19
    | exact resolve eq19 eq263007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263151 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq263007
       grind)
    | exact superpose eq263007 eq25
    | exact resolve eq25 eq263007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq263521 : y = (σ x) := by
    first
    | exact superpose eq130408 eq263151
    | exact resolve eq263151 eq130408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263151
  have eq263522 : y = (M.op x y) := by
    first
    | (have i₁ := eq263150
       have i₂ := eq254364 x
       grind)
    | exact superpose eq254364 eq263150
    | exact resolve eq263150 eq254364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254364 eq263150
  have eq263643 : y = (σ x) := by
    first
    | (have i₁ := eq263521
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq263521
    | exact resolve eq263521 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263521
  have eq263644 : x = (M.op x y) := by
    first
    | (have i₁ := eq263522
       have i₂ := eq263007
       grind)
    | exact superpose eq263007 eq263522
    | exact resolve eq263522 eq263007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263522
  have eq263708 : x = (σ x) := by
    first
    | (have i₁ := eq263643
       have i₂ := eq263007
       grind)
    | exact superpose eq263007 eq263643
    | exact resolve eq263643 eq263007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263007 eq263643
  have eq263823 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq263644 eq21
    | exact resolve eq21 eq263644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq264007 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq263823
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq263823
    | exact resolve eq263823 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq263823
  have eq264247 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq263708 eq27
    | exact resolve eq27 eq263708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq264388 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq130408 eq264247
    | exact resolve eq264247 eq130408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130408 eq264247
  have eq264441 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq264388
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq264388
    | exact resolve eq264388 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq264388
  have eq264483 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq263644 eq264441
    | exact resolve eq264441 eq263644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263644 eq264441
  have eq264555 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq263708 eq264007
    | exact resolve eq264007 eq263708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263708 eq264007
  have eq264557 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq264483 eq28
    | exact resolve eq28 eq264483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq264483
  have eq265157 : False := by grind
  exact eq265157

/-- `Equation3997`: `x ◇ y = (z ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation3997 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3997 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3997.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq218 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq92 X1 X1
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq222 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq218 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq223 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq222 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq225 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq223 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq223
    | (have j0 := eq223 X0 X1
       grind)
    | exact resolve eq223 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq229 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq225 X0 X1
       have j1 := eq221 X0 X1
       grind)
    | (have r₁ := eq225 X0 X1
       have r₂ := eq221 X0 X1
       grind)
    | (have r₁ := eq225 X0 (k X1 X0)
       have r₂ := eq221 X0 X1
       grind)
    | (have r₁ := eq225 X0 X0
       have r₂ := eq221 X0 X0
       grind)
    | exact resolve eq225 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq225
  have eq598 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq229 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq229
    | exact resolve eq229 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq229 x y
       grind)
    | exact superpose eq229 eq16
    | (have j1 := eq229 x y
       grind)
    | exact resolve eq16 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq628 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq598 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq598
    | (have j0 := eq598 X0 X1
       grind)
    | exact resolve eq598 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq598
  have eq633 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq628 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq628
    | exact resolve eq628 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq774 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq633 (τ X1) X0
       grind)
    | exact superpose eq633 eq18
    | (have j1 := eq633 (τ X1) X0
       grind)
    | exact resolve eq18 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq633
  have eq1080 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq774 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq774
    | exact resolve eq774 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq1133 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1080 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1080
    | (have j0 := eq1080 X0 X1
       grind)
    | exact resolve eq1080 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080
  have eq1214 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq612
       have i₂ := eq1133 y x
       grind)
    | exact superpose eq1133 eq612
    | (have j1 := eq1133 (σ y) (σ x)
       grind)
    | (have r₁ := eq612
       have r₂ := eq1133 y x
       grind)
    | exact resolve eq612 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1215 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1214
  have eq1275 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1215
  have eq1284 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq612
       have i₂ := eq1275
       grind)
    | exact superpose eq1275 eq612
    | exact resolve eq612 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq1275
  have eq1285 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1284
  have eq1286 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1285
  have eq1301 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1286
  have eq1311 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1301
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1301
    | exact resolve eq1301 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301
  have eq1317 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1311
       grind)
    | exact superpose eq1311 eq16
    | exact resolve eq16 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311
  have eq1372 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1317
       have i₂ := eq1133 y x
       grind)
    | exact superpose eq1133 eq1317
    | (have j1 := eq1133 y x
       grind)
    | (have r₁ := eq1317
       have r₂ := eq1133 y x
       grind)
    | exact resolve eq1317 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1373 : y = (M.op x x) := by grind
  clear eq1372
  have eq1378 : (M.op x y) = (k y x) := by grind
  clear eq1373
  have eq1428 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1317
       have i₂ := eq1378
       grind)
    | exact superpose eq1378 eq1317
    | exact resolve eq1317 eq1378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317 eq1378
  have eq1431 : False := by grind
  exact eq1431

/-- `Equation3997`: `x ◇ y = (z ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation3997 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3997 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3997.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq36
  have eq75 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k y x) := by
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
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq94
    | (have j0 := eq94 (σ X0) (σ X1)
       grind)
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq94 y x
       grind)
    | exact superpose eq94 eq72
    | (have j1 := eq94 y x
       grind)
    | exact resolve eq72 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq120 eq94
    | (have j0 := eq94 (σ y) (σ x)
       grind)
    | exact resolve eq94 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq124
       have r₂ := eq27
       grind)
    | exact resolve eq124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq27
    | exact resolve eq27 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq76
    | (have r₁ := eq76
       have r₂ := eq129
       grind)
    | exact resolve eq76 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq129
  have eq654 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq653
  have eq657 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq654 eq120
    | exact resolve eq120 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq661 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq657
  have eq666 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq661
       have r₂ := eq131
       grind)
    | exact resolve eq661 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq661
  have eq670 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq666 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq666
       grind)
    | exact resolve eq13 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq671 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq670 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq788 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq671 eq120
    | exact resolve eq120 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq671
  have eq791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq788
  have eq796 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq791
    | exact resolve eq791 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq798 : x = (M.op x y) := by
    first
    | (have r₁ := eq796
       have r₂ := eq27
       grind)
    | exact resolve eq796 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq800 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq798 eq20
    | exact resolve eq20 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq804 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq798 eq75
    | (have r₁ := eq75
       have r₂ := eq798
       grind)
    | exact resolve eq75 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq808 : x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq804
  have eq814 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq800
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq800
    | exact resolve eq800 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq829 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq98
    | (have j0 := eq98 X0 (M.op x y)
       grind)
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq859 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq798 eq829
    | (have j0 := eq829 X0
       grind)
    | exact resolve eq829 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq829
  have eq867 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq814 eq26
    | exact resolve eq26 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1118 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq808
       grind)
    | exact superpose eq808 eq72
    | exact resolve eq72 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq1125 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq814 eq1118
    | exact resolve eq1118 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq1127 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1125
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1125
    | exact resolve eq1125 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1125
  have eq1128 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq814 eq1127
    | exact resolve eq1127 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1131 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1128 eq94
    | (have j0 := eq94 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq94 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq1128
  have eq1132 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1131
  have eq1134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq867 eq1132
    | exact resolve eq1132 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1137 : x = (M.op x x) := by
    first
    | (have r₁ := eq1134
       have r₂ := eq27
       grind)
    | exact resolve eq1134 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq1145 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1137
       grind)
    | exact superpose eq1137 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1137
       grind)
    | exact resolve eq13 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq1146 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1145 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq1166 : (σ (k y x)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq859 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq859
    | (have j0 := eq859 y
       grind)
    | exact resolve eq859 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq859
  have eq1177 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq867 eq1166
    | exact resolve eq1166 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq1190 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1177
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq1177
    | exact resolve eq1177 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq1199 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq814 eq1190
    | exact resolve eq1190 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq1204 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq867 eq1199
    | exact resolve eq1199 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867 eq1199
  have eq1206 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1204
       have r₂ := eq27
       grind)
    | exact resolve eq1204 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1297 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1146 y
       grind)
    | exact superpose eq1146 eq72
    | exact resolve eq72 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1146
  have eq1302 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq814 eq1297
    | exact resolve eq1297 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq1297
  have eq1308 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1206 eq1302
    | exact resolve eq1302 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206 eq1302
  have eq1313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1308
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1308
    | exact resolve eq1308 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1308
  have eq1316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1313
    | exact resolve eq1313 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1313
  have eq1319 : False := by grind
  exact eq1319

/-- `Equation3997`: `x ◇ y = (z ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation3997 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3997 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3997.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq28
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq96 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq4086 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq96 X1 X0
       grind)
    | exact superpose eq96 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq96 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq96 (M.op X1 (σ X1)) X1
       grind)
    | exact resolve eq13 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq4113 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4086 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4086
  have eq4114 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4113 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4113
  have eq7831 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4114 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4114
    | exact resolve eq4114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7864 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq4114 X0 X1
       grind)
    | exact superpose eq4114 eq37
    | (have j1 := eq4114 X0 X1
       grind)
    | exact resolve eq37 eq4114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4114
  have eq7970 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7864 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7864
    | (have j0 := eq7864 X0 X1
       grind)
    | exact resolve eq7864 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7864
  have eq7978 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7831 X0 X1
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq7831
    | (have j0 := eq7831 X0 X1
       grind)
    | exact resolve eq7831 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7831
  have eq8043 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq7978 X1 X0
       grind)
    | exact superpose eq7978 eq11
    | (have j1 := eq7978 X1 X0
       grind)
    | exact resolve eq11 eq7978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7978
  have eq8165 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8043 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq8043
    | (have j0 := eq8043 X0 X1
       grind)
    | exact resolve eq8043 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8043
  have eq8392 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq8165 (τ X0) X1
       grind)
    | exact superpose eq8165 eq19
    | (have j1 := eq8165 (τ X0) X1
       grind)
    | exact resolve eq19 eq8165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq8165
  have eq8532 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7970 (τ X1) X0
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq7970
    | (have j0 := eq7970 (τ X0) X1
       grind)
    | exact resolve eq7970 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq7970
  have eq8673 : ∀ X0 X1 : G, X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8532 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8532
    | (have j0 := eq8532 X0 X1
       grind)
    | exact resolve eq8532 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8532
  have eq8714 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8673 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8673
    | (have j0 := eq8673 X0 X1
       grind)
    | exact resolve eq8673 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8673
  have eq9025 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq8714 X1 X0
       grind)
    | exact superpose eq8714 eq11
    | (have j1 := eq8714 (k X1 X0) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq8714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8714
  have eq9149 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9025 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq9025
    | (have j0 := eq9025 X0 X1
       grind)
    | exact resolve eq9025 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9025
  have eq9422 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9149 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9149
    | (have j0 := eq9149 (τ (σ X0)) (τ (σ (k X0 X1)))
       grind)
    | exact resolve eq9149 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9149
  have eq9604 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9422 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq9422
    | (have j0 := eq9422 X0 X1
       grind)
    | exact resolve eq9422 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9422
  have eq9615 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9604 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9604
    | (have j0 := eq9604 X0 X1
       grind)
    | exact resolve eq9604 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9604
  have eq10423 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8392 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8392
    | exact resolve eq8392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8392
  have eq10520 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10423 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq10423
    | (have j0 := eq10423 X0 X1
       grind)
    | exact resolve eq10423 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10423
  have eq10967 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9615 y x
       grind)
    | exact superpose eq9615 eq16
    | (have j1 := eq9615 x y
       grind)
    | exact resolve eq16 eq9615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9615
  have eq11110 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10967
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq10967
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq10967
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq10967
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq10967 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11111 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq10967
       have i₂ := eq10520 x y
       grind)
    | exact superpose eq10520 eq10967
    | (have j1 := eq10520 x y
       grind)
    | (have r₁ := eq10967
       have r₂ := eq10520 x y
       grind)
    | (have r₁ := eq10967
       have r₂ := eq10520 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq10967
       have r₂ := eq10520 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq10967 eq10520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10520 eq10967
  have eq11114 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by grind
  clear eq11111
  have eq11115 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq11114
  have eq11116 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq11110
  have eq11117 : x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq11116
  have eq11120 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11115
       grind)
    | exact superpose eq11115 eq16
    | exact resolve eq16 eq11115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11115
  have eq11121 : y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11120
       have r₂ := eq22 x
       grind)
    | exact resolve eq11120 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11120
  have eq11206 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq278 x y
       have i₂ := eq11121
       grind)
    | exact superpose eq11121 eq278
    | (have j0 := eq278 x y
       grind)
    | exact resolve eq278 eq11121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq11121
  have eq11223 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq11206
  have eq11224 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq11223
  have eq11231 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11117
       grind)
    | exact superpose eq11117 eq16
    | exact resolve eq16 eq11117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11117
  have eq11232 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11231
       have r₂ := eq22 x
       grind)
    | exact resolve eq11231 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11231
  have eq11325 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11224
       grind)
    | exact superpose eq11224 eq16
    | exact resolve eq16 eq11224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11224
  have eq11565 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11325
       have i₂ := eq11232
       grind)
    | exact superpose eq11232 eq11325
    | exact resolve eq11325 eq11232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11232 eq11325
  have eq11569 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq11565
  have eq11570 : (σ x) = (σ y) := by grind
  clear eq11569
  have eq11571 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11570
       grind)
    | exact superpose eq11570 eq16
    | exact resolve eq16 eq11570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11572 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11570
       grind)
    | exact superpose eq11570 eq10
    | exact resolve eq10 eq11570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11570
  have eq11666 : x = y := by
    first
    | (have i₁ := eq11572
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11572
    | exact resolve eq11572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11572
  have eq11667 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11571
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq11571
    | exact resolve eq11571 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq11571
  have eq11668 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11667
       have i₂ := eq11666
       grind)
    | exact superpose eq11666 eq11667
    | exact resolve eq11667 eq11666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11666 eq11667
  have eq11669 : False := by grind
  exact eq11669
