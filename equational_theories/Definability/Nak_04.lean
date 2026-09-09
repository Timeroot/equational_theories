import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3506`: `x ◇ x = y ◇ ((z ◇ w) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pyy_pxy_Equation3506 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3506 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3506.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X3)) := by
    intro X0 X1 X2 X3
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq24 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x x x
       have i₂ := eq9 X1 x x x
       grind)
    | (have i₁ := eq9 X0 (M.op (M.op x x) x) x x
       have i₂ := eq9 (M.op (M.op x x) x) X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq61 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq65 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq61 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq106 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X2) ∨ (M.op X2 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2
       have i₂ := eq24 X1 X0
       grind)
    | (have i₁ := eq14 X1 X2
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq14
    | (have j0 := eq14 X1 X2
       grind)
    | exact resolve eq14 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq113 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X2) ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq106 X0 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | (have r₁ := eq106 (M.op X1 X2) X1 X2
       have r₂ := eq12 X0 (M.op X1 X2)
       grind)
    | (have r₁ := eq106 X0 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq106 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq106 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq223 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq226 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq223 X0 X1
       have j1 := eq113 X0 X0 X1
       grind)
    | (have r₁ := eq223 X1 x
       have r₂ := eq113 x X1 x
       grind)
    | (have r₁ := eq223 X0 X0
       have r₂ := eq113 X0 X0 X0
       grind)
    | exact resolve eq223 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq223
  have eq565 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq226 (σ X0) (σ X1)
       grind)
    | exact superpose eq226 eq15
    | exact resolve eq15 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq565 X0 X1
       have i₂ := eq226 X0 X1
       grind)
    | exact superpose eq226 eq565
    | exact resolve eq565 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq565
  have eq573 : False := by grind
  exact eq573

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyy_pxx_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq17
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq40 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq40
    | exact resolve eq40 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq40
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq80 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq12
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq80 X0 (σ X0)
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq80 X0 X0
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq80 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq95 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq98 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq98
    | (have j0 := eq98 X0 X1
       grind)
    | exact resolve eq98 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq140 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 (σ X0) X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq21
    | exact resolve eq21 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100 x y
       grind)
    | exact superpose eq100 eq16
    | (have j1 := eq100 x y
       grind)
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq100 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1976 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq387
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq387
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq387 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq1977 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq1976
  have eq2078 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq397 (τ X0) (τ X1)
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq397
    | (have j0 := eq397 (τ X0) (τ X1)
       grind)
    | exact resolve eq397 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq2109 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2078 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2078
    | (have j0 := eq2078 X0 X1
       grind)
    | exact resolve eq2078 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078
  have eq2135 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2109 X0 X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq2109
    | (have j0 := eq2109 X0 X1
       grind)
    | exact resolve eq2109 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2109
  have eq2154 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2135 X0 X1
       have i₂ := eq44 X1
       grind)
    | exact superpose eq44 eq2135
    | (have j0 := eq2135 X0 X1
       grind)
    | exact resolve eq2135 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2135
  have eq2169 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2154 X0 X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq2154
    | (have j0 := eq2154 X0 X1
       grind)
    | exact resolve eq2154 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2154
  have eq2180 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2169 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2169
    | (have j0 := eq2169 X0 X1
       grind)
    | exact resolve eq2169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169
  have eq2183 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2180 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2180
    | (have j0 := eq2180 X0 X1
       grind)
    | exact resolve eq2180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180
  have eq2184 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2183 X0 X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq2183
    | (have j0 := eq2183 X0 X1
       grind)
    | exact resolve eq2183 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183
  have eq3833 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq85
    | (have r₁ := eq85 X0 (σ X0)
       have r₂ := eq42 X0
       grind)
    | exact resolve eq85 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3845 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (τ X0) X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq85
    | (have j0 := eq85 (τ X0) X1
       grind)
    | (have r₁ := eq85 (τ X0) X0
       have r₂ := eq44 X0
       grind)
    | exact resolve eq85 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq85
  have eq3846 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3845 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3845
    | (have j0 := eq3845 X0 X1
       grind)
    | exact resolve eq3845 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3845
  have eq3850 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3833 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3833
    | (have j0 := eq3833 X0 X1
       grind)
    | exact resolve eq3833 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3833
  have eq43799 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1977
       grind)
    | exact superpose eq1977 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1977
       grind)
    | exact resolve eq12 eq1977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977
  have eq43823 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq43799
  have eq43826 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have j1 := eq3846 y x
       grind)
    | (have r₁ := eq43823
       have r₂ := eq3846 x y
       grind)
    | (have r₁ := eq43823
       have r₂ := eq3846 y x
       grind)
    | exact resolve eq43823 eq3846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3846 eq43823
  have eq840156 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq397 x y
       have i₂ := eq43826
       grind)
    | exact superpose eq43826 eq397
    | (have j0 := eq397 x y
       grind)
    | exact resolve eq397 eq43826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq43826
  have eq840203 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq840156
  have eq840204 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq840203
  have eq840220 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq840204
       grind)
    | exact superpose eq840204 eq16
    | exact resolve eq16 eq840204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840222 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq82 x (σ y)
       have i₂ := eq840204
       grind)
    | exact superpose eq840204 eq82
    | (have j0 := eq82 x (σ y)
       grind)
    | (have r₁ := eq82 x (σ y)
       have r₂ := eq840204
       grind)
    | exact resolve eq82 eq840204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq840204
  have eq840341 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq840222
  have eq840366 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq840341
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq840341
    | exact resolve eq840341 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840341
  have eq840381 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq3850 x y
       grind)
    | (have r₁ := eq840366
       have r₂ := eq3850 x y
       grind)
    | (have r₁ := eq840366
       have r₂ := eq3850 y x
       grind)
    | exact resolve eq840366 eq3850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3850 eq840366
  have eq840412 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq840381
       grind)
    | exact superpose eq840381 eq10
    | exact resolve eq10 eq840381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840381
  have eq841077 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq840412
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq840412
    | exact resolve eq840412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840412
  have eq843836 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2184 x y
       have i₂ := eq841077
       grind)
    | exact superpose eq841077 eq2184
    | (have j0 := eq2184 x y
       grind)
    | (have r₁ := eq2184 x y
       have r₂ := eq841077
       grind)
    | exact resolve eq2184 eq841077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2184 eq841077
  have eq843856 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq843836
  have eq852293 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (M.op x x) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 y X0 x
       have i₂ := eq843856
       grind)
    | exact superpose eq843856 eq21
    | exact resolve eq21 eq843856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843856
  have eq852353 : ∀ X0 : G, (M.op x x) = (M.op y y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq852293 X0 x
       have i₂ := eq21 x x X0 x
       grind)
    | exact superpose eq21 eq852293
    | exact resolve eq852293 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852293
  have eq855689 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 y X0 y
       have i₂ := eq852353 X2
       grind)
    | exact superpose eq852353 eq21
    | (have j1 := eq852353 X2
       grind)
    | exact resolve eq21 eq852353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852353
  have eq855753 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X2
    first
    | (have i₁ := eq855689 X0 x X2
       have i₂ := eq21 x x X0 x
       grind)
    | exact superpose eq21 eq855689
    | (have j0 := eq855689 X0 x X0
       grind)
    | exact resolve eq855689 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq855689
  have eq861234 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq855753 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855753
  have eq861235 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq861234 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861234
  have eq861246 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq140 y X0 X1
       have i₂ := eq861235 y
       grind)
    | exact superpose eq861235 eq140
    | exact resolve eq140 eq861235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967801 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq840220
       have i₂ := eq861235 x
       grind)
    | exact superpose eq861235 eq840220
    | exact resolve eq840220 eq861235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840220
  have eq967804 : (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq967801
  have eq967810 : (σ (M.op x x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq967804
       have i₂ := eq861235 y
       grind)
    | exact superpose eq861235 eq967804
    | exact resolve eq967804 eq861235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967804
  have eq967815 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq861246 X0 X1
       have i₂ := eq967810
       grind)
    | exact superpose eq967810 eq861246
    | exact resolve eq861246 eq967810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861246 eq967810
  have eq968537 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq967815 X0 x
       have i₂ := eq140 x X0 x
       grind)
    | exact superpose eq140 eq967815
    | exact resolve eq967815 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq967815
  have eq976147 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq968537 (σ x)
       grind)
    | exact superpose eq968537 eq16
    | exact resolve eq16 eq968537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968537
  have eq976534 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq976147
       have i₂ := eq42 x
       grind)
    | exact superpose eq42 eq976147
    | exact resolve eq976147 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq976147
  have eq977127 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq976534
       have i₂ := eq861235 x
       grind)
    | exact superpose eq861235 eq976534
    | exact resolve eq976534 eq861235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861235 eq976534
  have eq977128 : False := by grind
  exact eq977128

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(Y,X) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyx_pyy_pxx_x_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq12 (σ x) (σ y)
       grind)
    | exact superpose eq12 eq9
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq16
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq31 : ∀ X0 : G, (σ (M.op x y)) ≠ (k (σ x) X0) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq19
       have i₂ := eq14 (σ x) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (σ x) X0
       grind)
    | (have r₁ := eq19
       have r₂ := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x X0)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 (σ X0)
       have i₂ := eq11 x X0
       grind)
    | exact superpose eq11 eq31
    | (have j0 := eq31 (σ X0)
       grind)
    | exact resolve eq31 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq76 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ X0)) ∨ (M.op x x) ≠ (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq54 X0
       have i₂ := eq14 x X0
       grind)
    | exact superpose eq14 eq54
    | (have j0 := eq54 X0
       have j1 := eq14 (σ x) (σ X0)
       grind)
    | (have r₁ := eq54 X0
       have r₂ := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ X0)) ∨ (M.op x x) ≠ (M.op x X0) ∨ (M.op x y) = (k x y) ∨ (M.op y x) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq76 X0
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq76
    | (have j0 := eq76 X0
       have j1 := eq12 x y
       grind)
    | (have r₁ := eq76 x
       have r₂ := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq76 X0
       have r₂ := eq12 (σ X0) (σ x)
       grind)
    | (have r₁ := eq76 X0
       have r₂ := eq12 (σ x) (σ X0)
       grind)
    | exact resolve eq76 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq275 : ∀ X0 : G, (M.op x x) ≠ (M.op x X0) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) ∨ (M.op y x) = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq271 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq500 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have j0 := eq275 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq501 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y x) = (M.op y y) := by grind
  clear eq500
  have eq513 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq54 y
       have i₂ := eq501
       grind)
    | exact superpose eq501 eq54
    | (have j0 := eq54 y
       grind)
    | exact resolve eq54 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq501
  have eq527 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op y x) = (M.op y y) := by grind
  clear eq513
  have eq528 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op y x) = (M.op y y) := by grind
  clear eq527
  have eq534 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (M.op y x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq528
       have i₂ := eq12 (σ x) (σ y)
       grind)
    | exact superpose eq12 eq528
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq528
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq528
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq528 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq538 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (M.op y x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq534
  have eq539 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (M.op y x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq538
  have eq541 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq539
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq539
    | exact resolve eq539 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq546 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq541
       grind)
    | exact superpose eq541 eq9
    | exact resolve eq9 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq577 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq546
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq546
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq546 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq579 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq577
  have eq580 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq579
  have eq595 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X0)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y y
       have i₂ := eq580
       grind)
    | exact superpose eq580 eq10
    | exact resolve eq10 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq608 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq595 X0
       have i₂ := eq10 X0 x y
       grind)
    | exact superpose eq10 eq595
    | exact resolve eq595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq609 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq608 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq623 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ x)) X0)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (σ y) (σ y)
       have i₂ := eq609
       grind)
    | exact superpose eq609 eq10
    | exact resolve eq10 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq639 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq623 X0
       have i₂ := eq10 X0 (σ x) (σ y)
       grind)
    | exact superpose eq10 eq623
    | exact resolve eq623 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq660 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X0)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op X1 (σ x)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 y x
       have i₂ := eq639 X1
       grind)
    | exact superpose eq639 eq10
    | (have j1 := eq639 X1
       grind)
    | exact resolve eq10 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq684 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 (σ x)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq660 X0 X1
       have i₂ := eq10 X0 x x
       grind)
    | exact superpose eq10 eq660
    | (have j0 := eq660 X0 X1
       grind)
    | exact resolve eq660 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq722 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 (σ x)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq19
       have i₂ := eq684 X0 X1
       grind)
    | exact superpose eq684 eq19
    | (have j1 := eq684 X0 (σ y)
       grind)
    | (have r₁ := eq19
       have r₂ := eq684 X0 X1
       grind)
    | exact resolve eq19 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq684
  have eq779 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 (σ x)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq722 X0 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq780 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq779 X0 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq870 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq9
       have i₂ := eq780 X0
       grind)
    | exact superpose eq780 eq9
    | (have j1 := eq780 X0
       grind)
    | exact resolve eq9 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq902 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op X0 y) = (M.op X0 x) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq870 X0
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq870
    | (have j0 := eq870 X0
       have j1 := eq12 x y
       grind)
    | exact resolve eq870 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq904 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op X0 y) = (M.op X0 x) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq902 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq905 : (M.op y x) = (M.op y y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq904 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq924 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X0)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y y
       have i₂ := eq905
       grind)
    | exact superpose eq905 eq10
    | exact resolve eq10 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq937 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq924 X0
       have i₂ := eq10 X0 x y
       grind)
    | exact superpose eq10 eq924
    | exact resolve eq924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq938 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq937 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq952 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ x)) X0)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (σ y) (σ y)
       have i₂ := eq938
       grind)
    | exact superpose eq938 eq10
    | exact resolve eq10 eq938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq968 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq952 X0
       have i₂ := eq10 X0 (σ x) (σ y)
       grind)
    | exact superpose eq10 eq952
    | exact resolve eq952 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq989 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X0)) ∨ (M.op X1 (σ x)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 y x
       have i₂ := eq968 X1
       grind)
    | exact superpose eq968 eq10
    | (have j1 := eq968 X1
       grind)
    | exact resolve eq10 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq1013 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op X1 (σ y)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 X1
       have i₂ := eq10 X0 x x
       grind)
    | exact superpose eq10 eq989
    | (have j0 := eq989 X0 X1
       grind)
    | exact resolve eq989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq1063 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (M.op X1 y) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (σ y)
       have i₂ := eq1013 X1 X0
       grind)
    | exact superpose eq1013 eq14
    | (have j0 := eq14 X0 (σ y)
       have j1 := eq1013 X1 X1
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq1013 X0 (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq1013 X0 (σ x)
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq1013 x X1
       grind)
    | exact resolve eq14 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1074 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq9
       have i₂ := eq1013 X0 (σ x)
       grind)
    | exact superpose eq1013 eq9
    | (have j1 := eq1013 X0 x
       grind)
    | exact resolve eq9 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq2553 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1063 (σ x) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq2583 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq2553 X0
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq2553
    | (have j0 := eq2553 X0
       grind)
    | exact resolve eq2553 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2553
  have eq2612 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 y) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1074 X0
       have i₂ := eq2583 X1
       grind)
    | exact superpose eq2583 eq1074
    | (have j0 := eq1074 X0
       have j1 := eq2583 X0
       grind)
    | exact resolve eq1074 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq2583
  have eq2641 : ∀ X1 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X1 y) = (M.op X1 x) := by
    intro X1
    first
    | (have j0 := eq2612 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2612
  have eq2662 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 y) = (M.op X0 x) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2641 X0
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq2641
    | (have j0 := eq2641 X0
       have j1 := eq12 x y
       grind)
    | exact resolve eq2641 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2641
  have eq2664 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq2662 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662
  have eq2665 : (M.op y x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq2664 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2664
  have eq2702 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X0)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y y
       have i₂ := eq2665
       grind)
    | exact superpose eq2665 eq10
    | exact resolve eq10 eq2665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2665
  have eq2723 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2702 X0
       have i₂ := eq10 X0 x y
       grind)
    | exact superpose eq10 eq2702
    | exact resolve eq2702 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702
  have eq2724 : (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq2723 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723
  have eq2742 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y x
       have i₂ := eq2724
       grind)
    | exact superpose eq2724 eq10
    | exact resolve eq10 eq2724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2744 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq2724
       grind)
    | exact superpose eq2724 eq14
    | (have j0 := eq14 x y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq2724
       grind)
    | exact resolve eq14 eq2724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724
  have eq2747 : (k x y) = (M.op x x) := by grind
  clear eq2744
  have eq2757 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq2742 X0
       have i₂ := eq10 X0 x x
       grind)
    | exact superpose eq10 eq2742
    | exact resolve eq2742 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2742
  have eq2806 : ∀ X0 X1 : G, (M.op y X1) = (M.op y (M.op (M.op X0 X1) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 y X1 X0
       have i₂ := eq2757 (M.op X0 X1)
       grind)
    | exact superpose eq2757 eq10
    | exact resolve eq10 eq2757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2942 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) x)) = (M.op X1 (M.op (M.op y X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 (M.op (M.op X2 X0) x) y
       have i₂ := eq2806 X2 X0
       grind)
    | exact superpose eq2806 eq10
    | exact resolve eq10 eq2806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2806
  have eq2955 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op X2 X0) x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2942 X0 X1 X2
       have i₂ := eq10 X1 X0 y
       grind)
    | exact superpose eq10 eq2942
    | exact resolve eq2942 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2942
  have eq3003 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X0) x)) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2955 X2 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq2955 X1 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq2955
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq2955 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3004 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) x)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2955 (M.op (M.op X3 X1) X0) X2 X0
       have i₂ := eq10 X0 X1 X3
       grind)
    | exact superpose eq10 eq2955
    | exact resolve eq2955 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3070 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op (M.op X2 X1) x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 (M.op (M.op X2 X1) x)
       have i₂ := eq2955 X1 X0 X2
       grind)
    | exact superpose eq2955 eq14
    | (have j0 := eq14 X0 (M.op (M.op X2 X1) x)
       grind)
    | (have r₁ := eq14 (M.op (M.op X2 X0) x) X0
       have r₂ := eq2955 X0 (M.op (M.op X2 X0) x) X2
       grind)
    | (have r₁ := eq14 X0 (M.op (M.op X2 X0) x)
       have r₂ := eq2955 X0 X0 X2
       grind)
    | exact resolve eq14 eq2955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3130 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3004 X0 X1 X2 X3
       have i₂ := eq2955 X1 X2 X0
       grind)
    | exact superpose eq2955 eq3004
    | exact resolve eq3004 eq2955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3004
  have eq3131 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3003 X0 X1 X2
       have i₂ := eq2955 X0 X1 X0
       grind)
    | exact superpose eq2955 eq3003
    | (have j0 := eq3003 X0 X1 X2
       grind)
    | exact resolve eq3003 eq2955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955 eq3003
  have eq3132 : ∀ X0 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X2) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have j0 := eq3131 X0 x X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3131
  have eq3280 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X2 X0) = (M.op X2 (M.op (k X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3130 X3 X0 X2 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq3130
    | (have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq3130 X0 X1 (M.op (M.op X3 X1) X0) X3
       have r₂ := eq14 (M.op (M.op X3 X1) X0) X1
       grind)
    | (have r₁ := eq3130 X0 X0 X0 X3
       have r₂ := eq14 X0 (M.op (M.op X3 X0) X0)
       grind)
    | exact resolve eq3130 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3130
  have eq3595 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq3132 (σ X1) (σ X0)
       grind)
    | exact superpose eq3132 eq11
    | (have j1 := eq3132 (σ X1) (σ X0)
       grind)
    | exact resolve eq11 eq3132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3132
  have eq4270 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op (M.op X1 X0) x)) := by
    intro X0 X1
    first
    | (have j0 := eq3070 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3070
  have eq4319 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (M.op (k X0 X1) x)) ∨ (M.op X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4270 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq4270
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq4270 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4270
  have eq4706 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (k X1 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3280 X1 X1 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3280
  have eq4809 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op (k X1 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 (M.op (k X1 X1) X2)
       have i₂ := eq4706 X0 X1 X2
       grind)
    | exact superpose eq4706 eq14
    | (have j0 := eq14 X0 (M.op (k X1 X1) X2)
       grind)
    | (have r₁ := eq14 (M.op (k X1 X1) X2) X1
       have r₂ := eq4706 (M.op (k X1 X1) X2) X1 X2
       grind)
    | (have r₁ := eq14 X1 (M.op (k X1 X1) X2)
       have r₂ := eq4706 X1 X1 X2
       grind)
    | exact resolve eq14 eq4706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4706
  have eq7347 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4809 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4809
  have eq7447 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4319 X0 X0
       have i₂ := eq7347 X0 x
       grind)
    | exact superpose eq7347 eq4319
    | (have j0 := eq4319 X0 X0
       grind)
    | exact resolve eq4319 eq7347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4319 eq7347
  have eq7475 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7447 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7447
  have eq7517 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq7475 (σ X0)
       grind)
    | exact superpose eq7475 eq11
    | exact resolve eq11 eq7475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7571 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7517 X0
       have i₂ := eq7475 X0
       grind)
    | exact superpose eq7475 eq7517
    | exact resolve eq7517 eq7475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7475 eq7517
  have eq24128 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq3595 x y
       grind)
    | exact superpose eq3595 eq9
    | (have j1 := eq3595 x y
       grind)
    | exact resolve eq9 eq3595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3595
  have eq24307 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq24128
       have i₂ := eq2747
       grind)
    | exact superpose eq2747 eq24128
    | exact resolve eq24128 eq2747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2747 eq24128
  have eq24396 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq24307
       have i₂ := eq2757 x
       grind)
    | exact superpose eq2757 eq24307
    | exact resolve eq24307 eq2757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24307
  have eq24397 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq24396
  have eq24435 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24397
       have i₂ := eq7571 x
       grind)
    | exact superpose eq7571 eq24397
    | exact resolve eq24397 eq7571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7571 eq24397
  have eq24471 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq24435
       grind)
    | exact superpose eq24435 eq9
    | exact resolve eq9 eq24435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24435
  have eq24592 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq24471
       have i₂ := eq2757 x
       grind)
    | exact superpose eq2757 eq24471
    | exact resolve eq24471 eq2757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2757 eq24471
  have eq24593 : False := by grind
  exact eq24593

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(Y,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_y_pyy_y_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  clear eq22
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
  have eq50 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq43
    | exact resolve eq43 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq70 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq64 sF2
       grind)
    | exact superpose eq64 eq67
    | exact resolve eq67 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq75 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq92
    | exact resolve eq92 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq96 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
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
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq108 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq64 sF3
       grind)
    | exact superpose eq64 eq104
    | exact resolve eq104 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq64 y
       grind)
    | exact superpose eq64 eq108
    | exact resolve eq108 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq108
  have eq146 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq16
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq241 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq239 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq239
    | exact resolve eq239 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq246 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq249 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq246 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq246
    | exact resolve eq246 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq9324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9325 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq9324
    | exact resolve eq9324 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9324
  have eq9336 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq9325
       have r₂ := eq27
       grind)
    | exact resolve eq9325 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9325
  have eq9340 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq9336
    | exact resolve eq9336 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9336
  have eq9342 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq9340
    | exact resolve eq9340 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9340
  have eq9346 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq9342 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq9342
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq9342
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq9342
       grind)
    | exact resolve eq13 eq9342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9348 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq9342 eq54
    | exact resolve eq54 eq9342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9356 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq249 eq9348
    | exact resolve eq9348 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9348
  have eq9358 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq9346
       have r₂ := eq26
       grind)
    | exact resolve eq9346 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9346
  have eq9925 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq9358 eq97
    | exact resolve eq97 eq9358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq9358
  have eq9933 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9925
  have eq9958 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9933 eq9356
    | exact resolve eq9356 eq9933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9356 eq9933
  have eq9972 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq9958
  have eq10100 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq9972 eq9342
    | exact resolve eq9342 eq9972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9342 eq9972
  have eq10113 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq10100
  have eq10117 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10113
       have r₂ := eq27
       grind)
    | exact resolve eq10113 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10113
  have eq10124 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 y
       have i₂ := eq10117
       grind)
    | exact superpose eq10117 eq54
    | exact resolve eq54 eq10117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10132 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq241 eq10124
    | exact resolve eq10124 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10124
  have eq10250 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10132 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10132
    | (have j0 := eq10132 x
       grind)
    | exact resolve eq10132 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10283 : (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq10132 y
       grind)
    | exact superpose eq10132 eq110
    | exact resolve eq110 eq10132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq10300 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq10250
       grind)
    | exact superpose eq10250 eq70
    | exact resolve eq70 eq10250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq10250
  have eq10333 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10300
    | exact resolve eq10300 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10300
  have eq10463 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq10333 eq54
    | exact resolve eq54 eq10333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10809 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10283
       have i₂ := eq10117
       grind)
    | exact superpose eq10117 eq10283
    | exact resolve eq10283 eq10117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10117 eq10283
  have eq10871 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10809
  have eq10877 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10871
    | exact resolve eq10871 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10871
  have eq10891 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x y)) X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10877 eq14
    | exact resolve eq14 eq10877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10877
  have eq11731 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10891 eq10463
    | exact resolve eq10463 eq10891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10463 eq10891
  have eq11768 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq11731 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11731
  have eq11788 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11768
    | (have j0 := eq11768 (σ x)
       grind)
    | exact resolve eq11768 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11768
  have eq11864 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11788 eq10333
    | exact resolve eq10333 eq11788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10333 eq11788
  have eq11882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11864
  have eq11892 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11882
       have r₂ := eq27
       grind)
    | exact resolve eq11882 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11882
  have eq11896 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11892 eq76
    | (have r₁ := eq76
       have r₂ := eq11892
       grind)
    | exact resolve eq76 eq11892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11900 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq11896
  have eq12067 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11900 eq58
    | exact resolve eq58 eq11900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11900
  have eq12094 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq12067
    | exact resolve eq12067 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12067
  have eq12133 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12094 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq12094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12094
  have eq12147 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq12133
    | exact resolve eq12133 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12133
  have eq12150 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12147
       have r₂ := eq11892
       grind)
    | exact resolve eq12147 eq11892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12147
  have eq12462 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12150 eq58
    | exact resolve eq58 eq12150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12150
  have eq12483 : (k x y) = (M.op y y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq146 eq12462
    | exact resolve eq12462 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12462
  have eq12654 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq12483
       grind)
    | exact superpose eq12483 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq12483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12483
  have eq12657 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq12654
       have r₂ := eq12 x y
       grind)
    | exact resolve eq12654 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12654
  have eq12666 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12657
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12657
    | exact resolve eq12657 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12657
  have eq12669 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12666
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12666
    | exact resolve eq12666 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12666
  have eq12671 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ y = (k x y) := by
    first
    | (have r₁ := eq12669
       have r₂ := eq75
       grind)
    | exact resolve eq12669 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12669
  have eq13052 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12671
       have i₂ := eq10132 y
       grind)
    | exact superpose eq10132 eq12671
    | exact resolve eq12671 eq10132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10132 eq12671
  have eq13079 : (M.op x y) = (M.op y x) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13052
  have eq13091 : (M.op x y) = (M.op y x) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13079
       have r₂ := eq75
       grind)
    | exact resolve eq13079 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq13079
  have eq13098 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (M.op y y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq13091
       grind)
    | exact superpose eq13091 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq13091
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq13091
       grind)
    | exact resolve eq13 eq13091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13100 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 y
       have i₂ := eq13091
       grind)
    | exact superpose eq13091 eq54
    | exact resolve eq54 eq13091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13109 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq241 eq13100
    | exact resolve eq13100 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13100
  have eq13111 : (k x y) = (M.op y y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13098
       have r₂ := eq18
       grind)
    | exact resolve eq13098 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13098
  have eq13685 : y ≠ (M.op y y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13111
  have eq13703 : y ≠ (M.op y x) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13685
       have i₂ := eq13109 y
       grind)
    | exact superpose eq13109 eq13685
    | exact resolve eq13685 eq13109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13109 eq13685
  have eq13706 : y ≠ (M.op y x) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13703
  have eq13709 : y ≠ (M.op x y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13706
       have i₂ := eq13091
       grind)
    | exact superpose eq13091 eq13706
    | exact resolve eq13706 eq13091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13091 eq13706
  have eq13712 : y ≠ (M.op x y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13709
  have eq13713 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13712
       have r₂ := eq11892
       grind)
    | exact resolve eq13712 eq11892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11892 eq13712
  have eq13814 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq13713
       grind)
    | exact superpose eq13713 eq44
    | exact resolve eq44 eq13713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq13713
  have eq13838 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13814
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13814
    | exact resolve eq13814 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13814
  have eq13862 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13838 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq13838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13863 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13862
  have eq13869 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13863
    | exact resolve eq13863 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13863
  have eq13870 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq13869
  have eq13882 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13870
    | exact resolve eq13870 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13870
  have eq13896 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13882 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq13882
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq13882
       grind)
    | exact resolve eq13 eq13882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13898 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq13882 eq54
    | exact resolve eq54 eq13882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13912 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq249 eq13898
    | exact resolve eq13898 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13898
  have eq13914 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13896
       have r₂ := eq26
       grind)
    | exact resolve eq13896 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13896
  have eq14406 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13914 eq13838
    | exact resolve eq13838 eq13914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13838
  have eq14408 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14406
  have eq14449 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14408 eq13912
    | exact resolve eq13912 eq14408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13912 eq14408
  have eq14469 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14449
  have eq14600 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14469 eq13882
    | exact resolve eq13882 eq14469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13882 eq14469
  have eq14617 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14600
  have eq14624 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq14617 eq27
    | exact resolve eq27 eq14617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq14626 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq14617 eq76
    | (have r₁ := eq76
       have r₂ := eq14617
       grind)
    | exact resolve eq76 eq14617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq14628 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq14617 eq249
    | exact resolve eq249 eq14617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq14617
  have eq14630 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq14626
  have eq15137 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq14630 eq58
    | exact resolve eq58 eq14630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14630
  have eq15161 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x y) := by
    first
    | exact superpose eq29 eq15137
    | exact resolve eq15137 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15137
  have eq15271 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq15161 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq15161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15273 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ y = (k x y) := by
    intro X0 X1
    first
    | exact superpose eq15161 eq54
    | exact resolve eq54 eq15161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15286 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (k x y) := by
    intro X0
    first
    | exact superpose eq14628 eq15273
    | exact resolve eq15273 eq14628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14628 eq15273
  have eq15288 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq15271
    | exact resolve eq15271 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15271
  have eq15292 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | (have r₁ := eq15288
       have r₂ := eq13914
       grind)
    | exact resolve eq15288 eq13914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13914 eq15288
  have eq15791 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ y = (k x y) := by
    first
    | exact superpose eq15286 eq146
    | exact resolve eq146 eq15286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15286
  have eq16011 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ y = (k x y) := by
    first
    | exact superpose eq15292 eq58
    | exact resolve eq58 eq15292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq15292
  have eq16031 : (k x y) = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq146 eq16011
    | exact resolve eq16011 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq16011
  have eq16076 : y ≠ (M.op y y) ∨ y = (k x y) := by grind
  clear eq16031
  have eq16129 : (τ (σ y)) = (M.op y y) ∨ y = (k x y) ∨ y = (k x y) := by
    first
    | exact superpose eq15161 eq15791
    | exact resolve eq15791 eq15161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15161 eq15791
  have eq16178 : (τ (σ y)) = (M.op y y) ∨ y = (k x y) := by grind
  clear eq16129
  have eq16190 : y = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq29 eq16178
    | exact resolve eq16178 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16178
  have eq16193 : y = (k x y) := by
    first
    | (have r₁ := eq16190
       have r₂ := eq16076
       grind)
    | exact resolve eq16190 eq16076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16076 eq16190
  have eq16214 : y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq16193
       grind)
    | exact superpose eq16193 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq16193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16215 : y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq16214
  have eq16217 : y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16215
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16215
    | exact resolve eq16215 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16215
  have eq16228 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16217
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16217
    | exact resolve eq16217 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16217
  have eq16282 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq16228
       grind)
    | exact superpose eq16228 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq16228
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16228
       grind)
    | exact resolve eq13 eq16228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16284 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 y
       have i₂ := eq16228
       grind)
    | exact superpose eq16228 eq54
    | exact resolve eq54 eq16228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq16294 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq241 eq16284
    | exact resolve eq16284 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq16284
  have eq16296 : (k x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16282
       have r₂ := eq18
       grind)
    | exact resolve eq16282 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq16282
  have eq16299 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16296
       have i₂ := eq16193
       grind)
    | exact superpose eq16193 eq16296
    | exact resolve eq16296 eq16193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16193 eq16296
  have eq16505 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16299
       have i₂ := eq16294 y
       grind)
    | exact superpose eq16294 eq16299
    | exact resolve eq16299 eq16294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16294 eq16299
  have eq16524 : y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq16505
  have eq16603 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16228
       have i₂ := eq16524
       grind)
    | exact superpose eq16524 eq16228
    | exact resolve eq16228 eq16524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16228 eq16524
  have eq16624 : y = (M.op x y) := by grind
  clear eq16603
  have eq16635 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq16624 eq20
    | exact resolve eq20 eq16624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq16624
  have eq16762 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq16635
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16635
    | exact resolve eq16635 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16635
  have eq16792 : False := by grind
  exact eq16792

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq75 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 (M.op (M.op X2 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 (M.op (M.op X3 X1) X0)
       have i₂ := eq64 X0 X1 X2 X3
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X2) X1) ∨ (M.op (M.op (M.op X0 X1) X2) X1) = (k (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    grind
  have eq85 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X1) = (k (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq76 X0 X1 X2
       have j1 := eq75 (M.op (M.op X0 X1) X2) X1 X0 X2
       grind)
    | (have r₁ := eq76 X0 X1 X2
       have r₂ := eq75 (M.op (M.op X0 X1) X2) X1 X2 x
       grind)
    | exact resolve eq76 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq112 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq113 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 X0) X2)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    grind
  clear eq75
  have eq390 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X0) X2)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq389 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq424 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = X0 ∨ (M.op (M.op X1 X0) X2) = X0 ∨ (M.op X0 (M.op (M.op X1 X0) X2)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) X2)
       have i₂ := eq390 X0 X1 X2
       grind)
    | exact superpose eq390 eq14
    | (have j0 := eq14 X0 X0
       have j1 := eq390 X0 X1 X2
       grind)
    | exact resolve eq14 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq433 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = X0 ∨ (M.op (M.op X1 X0) X2) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq424 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq443 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X1 X0) X2) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq433 X0 X1 X2
       have i₂ := eq64 X2 X0 X0 X1
       grind)
    | exact superpose eq64 eq433
    | (have j0 := eq433 X0 X1 X2
       grind)
    | exact resolve eq433 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq433
  have eq453 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (M.op X1 X0) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq443 X0 X1 X2
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq443 X1 X1 X2
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq443 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq472 : ∀ X0 X1 X2 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (M.op X1 (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq453 (τ X0) X1 X2
       grind)
    | exact superpose eq453 eq18
    | (have j1 := eq453 (τ X0) X1 X2
       grind)
    | exact resolve eq18 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq453
  have eq477 : ∀ X0 X1 X2 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (M.op X1 (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq472 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq472
    | (have j0 := eq472 X0 X1 X2
       grind)
    | exact resolve eq472 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq2206 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (M.op X1 X0) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq477 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq477
    | exact resolve eq477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq2245 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2206 X0 X1 X2
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2206
    | (have j0 := eq2206 X0 X1 X2
       grind)
    | exact resolve eq2206 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206
  have eq2270 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq85 x X0 x
       have i₂ := eq2245 X0 x x
       grind)
    | exact superpose eq2245 eq85
    | (have j1 := eq2245 X0 x x
       grind)
    | exact resolve eq85 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq2245
  have eq2323 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq2270 X0
       grind)
    | exact superpose eq2270 eq10
    | (have j1 := eq2270 X0
       grind)
    | exact resolve eq10 eq2270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270
  have eq2362 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2323 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2323
    | (have j0 := eq2323 X0
       grind)
    | exact resolve eq2323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2323
  have eq2363 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2362 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362
  have eq2398 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2363 (σ X0)
       grind)
    | exact superpose eq2363 eq15
    | exact resolve eq15 eq2363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2417 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2398 X0
       have i₂ := eq2363 X0
       grind)
    | exact superpose eq2363 eq2398
    | exact resolve eq2398 eq2363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2363 eq2398
  have eq2489 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq112 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq26814 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq113 X0 X1
       grind)
    | exact superpose eq113 eq12
    | (have j1 := eq113 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq113 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq113 X0 (M.op (σ X0) X1)
       grind)
    | exact resolve eq12 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq26859 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26814 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26814
  have eq30091 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26859 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26859
    | exact resolve eq26859 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30128 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq26859 X0 X1
       grind)
    | exact superpose eq26859 eq29
    | (have j1 := eq26859 X0 X1
       grind)
    | exact resolve eq29 eq26859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq26859
  have eq30205 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30128 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30128
    | (have j0 := eq30128 X0 X1
       grind)
    | exact resolve eq30128 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30128
  have eq30222 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30091 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq30091
    | (have j0 := eq30091 X0 X1
       grind)
    | exact resolve eq30091 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq30091
  have eq30330 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq30222 X0 X1
       grind)
    | exact superpose eq30222 eq11
    | (have j1 := eq30222 X0 X1
       grind)
    | exact resolve eq11 eq30222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30222
  have eq30488 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30330 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq30330
    | (have j0 := eq30330 X0 X1
       grind)
    | exact resolve eq30330 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30330
  have eq30601 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq30488 X0 (τ X1)
       grind)
    | exact superpose eq30488 eq19
    | (have j1 := eq30488 X0 (τ X1)
       grind)
    | exact resolve eq19 eq30488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30488
  have eq30923 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) X1)
       have i₂ := eq30205 X0 X1
       grind)
    | exact superpose eq30205 eq11
    | (have j1 := eq30205 X0 X1
       grind)
    | exact resolve eq11 eq30205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30205
  have eq31033 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30923 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq30923
    | (have j0 := eq30923 X0 X1
       grind)
    | exact resolve eq30923 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq30923
  have eq31203 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq31033 X0 (σ X1)
       grind)
    | exact superpose eq31033 eq15
    | (have j1 := eq31033 X0 (σ X1)
       grind)
    | exact resolve eq15 eq31033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31033
  have eq31267 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31203 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq31203
    | (have j0 := eq31203 X0 X1
       grind)
    | exact resolve eq31203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31203
  have eq32601 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30601 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30601
    | exact resolve eq30601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30601
  have eq32719 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32601 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq32601
    | (have j0 := eq32601 X0 X1
       grind)
    | exact resolve eq32601 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32601
  have eq33056 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31267 x y
       grind)
    | exact superpose eq31267 eq16
    | (have j1 := eq31267 x y
       grind)
    | exact resolve eq16 eq31267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31267
  have eq33255 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33056
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq33056
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq33056
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq33056
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq33056 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33256 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq33056
       have i₂ := eq32719 y x
       grind)
    | exact superpose eq32719 eq33056
    | (have j1 := eq32719 y x
       grind)
    | (have r₁ := eq33056
       have r₂ := eq32719 y x
       grind)
    | (have r₁ := eq33056
       have r₂ := eq32719 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq33056
       have r₂ := eq32719 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq33056 eq32719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32719 eq33056
  have eq33259 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq33256
  have eq33260 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq33259
  have eq33261 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq33255
  have eq33262 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq33261
  have eq33266 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33260
       grind)
    | exact superpose eq33260 eq16
    | exact resolve eq16 eq33260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33260
  have eq33267 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq33266
       have r₂ := eq2417 x
       grind)
    | exact resolve eq33266 eq2417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33266
  have eq33272 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2489 x y
       have i₂ := eq33267
       grind)
    | exact superpose eq33267 eq2489
    | (have j0 := eq2489 x y
       grind)
    | exact resolve eq2489 eq33267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2489 eq33267
  have eq33281 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33272
  have eq33282 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq33281
  have eq33287 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33262
       grind)
    | exact superpose eq33262 eq16
    | exact resolve eq16 eq33262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33262
  have eq33288 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq33287
       have r₂ := eq2417 x
       grind)
    | exact resolve eq33287 eq2417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33287
  have eq33316 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33282
       grind)
    | exact superpose eq33282 eq16
    | exact resolve eq16 eq33282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33282
  have eq33370 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq33316
       have i₂ := eq33288
       grind)
    | exact superpose eq33288 eq33316
    | exact resolve eq33316 eq33288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33288 eq33316
  have eq33379 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq33370
  have eq33380 : (σ x) = (σ y) := by grind
  clear eq33379
  have eq33381 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33380
       grind)
    | exact superpose eq33380 eq16
    | exact resolve eq16 eq33380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33382 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq33380
       grind)
    | exact superpose eq33380 eq10
    | exact resolve eq10 eq33380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33380
  have eq33453 : x = y := by
    first
    | (have i₁ := eq33382
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq33382
    | exact resolve eq33382 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33382
  have eq33454 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq33381
       have i₂ := eq2417 x
       grind)
    | exact superpose eq2417 eq33381
    | exact resolve eq33381 eq2417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417 eq33381
  have eq33462 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq33454
       have i₂ := eq33453
       grind)
    | exact superpose eq33453 eq33454
    | exact resolve eq33454 eq33453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33453 eq33454
  have eq33463 : False := by grind
  exact eq33463

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyy_pxy_y_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq57
    | (have j0 := eq57 (σ X0) (σ X1)
       grind)
    | exact resolve eq57 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq84 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq83
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq84
    | exact resolve eq84 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq84
  have eq96 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq92 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92
    | exact resolve eq92 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq127 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq16
    | (have j1 := eq68 x y
       grind)
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq158 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X2 (σ X0) X1 (σ X0)
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq25
    | exact resolve eq25 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq127
       have i₂ := eq96 x
       grind)
    | exact superpose eq96 eq127
    | exact resolve eq127 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq475 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq474
       have i₂ := eq96 y
       grind)
    | exact superpose eq96 eq474
    | exact resolve eq474 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq508 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq475
       have i₂ := eq57 x y
       grind)
    | exact superpose eq57 eq475
    | (have j1 := eq57 y x
       grind)
    | exact resolve eq475 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq475
  have eq509 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq508
  have eq1943 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq509
       grind)
    | exact superpose eq509 eq10
    | exact resolve eq10 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq1976 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1943
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq1943
    | exact resolve eq1943 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943
  have eq1977 : (M.op x x) = (M.op y y) := by grind
  clear eq1976
  have eq2042 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq158 y X0 X1
       have i₂ := eq1977
       grind)
    | exact superpose eq1977 eq158
    | exact resolve eq158 eq1977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2050 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 y X0 y
       have i₂ := eq1977
       grind)
    | exact superpose eq1977 eq25
    | exact resolve eq25 eq1977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977
  have eq2061 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq2050 X0 x
       have i₂ := eq25 x x X0 x
       grind)
    | exact superpose eq25 eq2050
    | exact resolve eq2050 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2050
  have eq2069 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2042 X0 x
       have i₂ := eq158 x X0 x
       grind)
    | exact superpose eq158 eq2042
    | exact resolve eq2042 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq2042
  have eq2538 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2069 (σ x)
       grind)
    | exact superpose eq2069 eq16
    | exact resolve eq16 eq2069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2069
  have eq2554 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2538
       have i₂ := eq96 x
       grind)
    | exact superpose eq96 eq2538
    | exact resolve eq2538 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq2538
  have eq2584 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2554
       have i₂ := eq2061 x
       grind)
    | exact superpose eq2061 eq2554
    | exact resolve eq2554 eq2061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061 eq2554
  have eq2585 : False := by grind
  exact eq2585

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxy_x_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq22
    | exact resolve eq22 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq57
    | (have j0 := eq57 (σ X0) (σ X1)
       grind)
    | exact resolve eq57 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq83 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq84 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq83
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq84
    | exact resolve eq84 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq84
  have eq96 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq92 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92
    | exact resolve eq92 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (k X0 (σ X1))
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq92
    | exact resolve eq92 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq103 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq10
    | exact resolve eq10 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op (M.op X2 X1) X3) X0) = (k (M.op (M.op X2 X1) X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) X3) X0
       have i₂ := eq25 X3 X1 X0 X2
       grind)
    | exact superpose eq25 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X3 X1) X0)
       have r₂ := eq25 X0 X1 (M.op (M.op X3 X1) X0) X3
       grind)
    | (have r₁ := eq12 (M.op (M.op X3 X1) X0) X1
       have r₂ := eq25 X0 X1 X1 X3
       grind)
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X1) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (M.op X3 (M.op (M.op X0 X1) X2)) = (k X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 (M.op (M.op X0 X1) X2)
       have i₂ := eq25 X2 X1 (M.op (M.op X0 X1) X2) X0
       grind)
    | exact superpose eq25 eq12
    | (have j0 := eq12 X3 (M.op (M.op X0 X1) X2)
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X3 X1) X0)
       have r₂ := eq25 X0 X1 (M.op (M.op X3 X1) X0) X3
       grind)
    | (have r₁ := eq12 (M.op (M.op X3 X1) X0) X1
       have r₂ := eq25 X0 X1 X1 X3
       grind)
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X1) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (M.op X3 X1) = (k X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq112 X0 X1 X2 X3
       have i₂ := eq25 X2 X1 X3 X0
       grind)
    | exact superpose eq25 eq112
    | (have j0 := eq112 X0 X1 X2 X3
       grind)
    | (have r₁ := eq112 X0 X1 X2 (M.op (M.op X3 X1) X0)
       have r₂ := eq25 X0 X1 (M.op (M.op X0 X1) X2) X3
       grind)
    | (have r₁ := eq112 X0 (M.op (M.op X3 X1) X0) X2 X1
       have r₂ := eq25 X0 X1 (M.op (M.op X0 (M.op (M.op X3 X1) X0)) X2) X3
       grind)
    | exact resolve eq112 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq124 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (σ X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq68
    | exact resolve eq68 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq168 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) X1) ≠ (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq661 : ∀ X0 X1 X2 X3 : G, (M.op X3 (k X0 (σ X1))) = (M.op X3 (M.op (M.op (k X0 (σ X1)) (σ X2)) X3)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (k X0 (σ X1)) (σ X2)
       have i₂ := eq124 X0 X1 X2
       grind)
    | exact superpose eq124 eq9
    | (have j1 := eq124 X0 X1 X2
       grind)
    | exact resolve eq9 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq666 : ∀ X0 X1 X2 X3 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (M.op X3 (σ X2)) = (M.op X3 (k X0 (σ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq661 X0 X1 X2 X3
       have i₂ := eq9 X3 (σ X2) (k X0 (σ X1))
       grind)
    | exact superpose eq9 eq661
    | (have j0 := eq661 X0 X1 X2 X3
       grind)
    | exact resolve eq661 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq957 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op (M.op (M.op X1 (τ X0)) X2) (τ X0)) = (k (M.op (M.op X1 (τ X0)) X2) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq110 (τ X0) (τ X0) X2 x
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq110
    | (have j0 := eq110 (τ X0) (τ X0) X1 X2
       grind)
    | exact resolve eq110 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq965 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (τ X0)) X2) (τ X0)) = (k (M.op (M.op X1 (τ X0)) X2) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq957 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1072 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq114 X1 X0 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq2979 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq168 X1 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq168
    | (have j0 := eq168 X1 (σ X0)
       grind)
    | exact resolve eq168 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq3512 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) = (k (M.op (τ (M.op X0 X0)) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq965 X0 (τ X0) x
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq965
    | exact resolve eq965 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq3530 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) X0) = (k (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq965 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq965
    | exact resolve eq965 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq3556 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X4) (M.op (M.op X2 X1) X3)) = (k (M.op (M.op X0 X1) X4) (M.op (M.op X2 X1) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3530 (M.op (M.op X3 X1) X0) X2 X2
       have i₂ := eq25 X0 X1 X2 X3
       grind)
    | exact superpose eq25 eq3530
    | exact resolve eq3530 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3530
  have eq3623 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X4) X1) = (k (M.op (M.op X0 X1) X4) (M.op (M.op X2 X1) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3556 X0 X1 X2 X3 X4
       have i₂ := eq25 X3 X1 (M.op (M.op X0 X1) X4) X2
       grind)
    | exact superpose eq25 eq3556
    | exact resolve eq3556 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3556
  have eq4006 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (M.op X1 (τ X0)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 (τ X0)) X2)
       have i₂ := eq1072 (τ X0) X1 X2
       grind)
    | exact superpose eq1072 eq17
    | exact resolve eq17 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq4028 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (σ (M.op (M.op X1 (τ X0)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4006 X0 X1 X2
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq4006
    | exact resolve eq4006 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq4006
  have eq48457 : ∀ X0 X1 X2 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2979 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq2979
    | exact resolve eq2979 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2979
  have eq48584 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48457 X0 X1 X2
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq48457
    | (have j0 := eq48457 X0 X1 X2
       grind)
    | exact resolve eq48457 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq48457
  have eq48604 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq48584 X0 X1 X2
       have j1 := eq666 X0 X1 X2 x
       grind)
    | (have r₁ := eq48584 X0 X1 X2
       have r₂ := eq666 X0 X1 X2 (k X0 (σ X1))
       grind)
    | exact resolve eq48584 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666 eq48584
  have eq49231 : ∀ X0 X1 X2 : G, (σ (k X1 (k X0 X2))) = (M.op (σ X1) (k (σ X0) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48604 (σ X0) X2 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48604
    | exact resolve eq48604 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49309 : ∀ X0 X1 X2 : G, (σ (τ (k X0 (k (σ (τ X1)) X2)))) = (M.op (σ (τ X0)) (k X1 (σ (τ X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48604 X1 (τ X2) (τ X0)
       have i₂ := eq38 (τ X1) X2 X0
       grind)
    | exact superpose eq38 eq48604
    | exact resolve eq48604 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq48604
  have eq49630 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (k X1 X2)) = (σ (τ (k X0 (k (σ (τ X1)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49309 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq49309
    | exact resolve eq49309 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49309
  have eq49689 : ∀ X0 X1 X2 : G, (σ (k X1 (k X0 X2))) = (M.op (σ X1) (σ (k X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49231 X0 X1 X2
       have i₂ := eq15 X0 X2
       grind)
    | exact superpose eq15 eq49231
    | exact resolve eq49231 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49231
  have eq49743 : ∀ X0 X1 X2 : G, (k X0 (k (σ (τ X1)) X2)) = (M.op (σ (τ X0)) (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49630 X0 X1 X2
       have i₂ := eq11 (k X0 (k (σ (τ X1)) X2))
       grind)
    | exact superpose eq11 eq49630
    | exact resolve eq49630 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49630
  have eq49801 : ∀ X0 X1 X2 : G, (k X0 (k (σ (τ X1)) X2)) = (M.op X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49743 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49743
    | exact resolve eq49743 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49743
  have eq49834 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (M.op X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49801 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq49801
    | exact resolve eq49801 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49801
  have eq49920 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op (M.op (M.op X0 X1) X2) X1)) = (M.op X3 (M.op (M.op (M.op X0 X1) X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49834 X0 (M.op (M.op X0 X1) x) (M.op (M.op X2 X1) X3)
       have i₂ := eq3623 X0 X1 X2 X3 x
       grind)
    | exact superpose eq3623 eq49834
    | exact resolve eq49834 eq3623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3623
  have eq49938 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 X1))) = (M.op X2 (σ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49834 X0 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq49834
    | exact resolve eq49834 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50240 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (k X3 (M.op (M.op (M.op X0 X1) X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49920 X0 X1 X2 X3
       have i₂ := eq25 X1 X2 X3 (M.op X0 X1)
       grind)
    | exact superpose eq25 eq49920
    | exact resolve eq49920 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49920
  have eq75877 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X0 X1))) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49938 x (M.op (M.op (M.op X0 X1) X2) X1) X2
       have i₂ := eq50240 X0 X1 X2 x
       grind)
    | exact superpose eq50240 eq49938
    | exact resolve eq49938 eq50240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49938 eq50240
  have eq80396 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (M.op X1 (τ X0)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75877 (M.op X1 (τ X0)) X2 X0
       have i₂ := eq4028 X0 X1 X2
       grind)
    | exact superpose eq4028 eq75877
    | exact resolve eq75877 eq4028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4028 eq75877
  have eq81665 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X0 X0) X4)) = (M.op X1 (σ (M.op (M.op X2 (τ X0)) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X4 (σ (M.op (M.op X2 (τ X0)) X3)) X1 X0
       have i₂ := eq80396 X0 X2 X3
       grind)
    | exact superpose eq80396 eq25
    | exact resolve eq25 eq80396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80396
  have eq81873 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 (σ (M.op (M.op X2 (τ X0)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq81665 X0 X1 X2 X3 x
       have i₂ := eq25 x X0 X1 X0
       grind)
    | exact superpose eq25 eq81665
    | exact resolve eq81665 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81665
  have eq85269 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X2 X0) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq81873 (σ X0) X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81873
    | exact resolve eq81873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81873
  have eq107489 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ (k X0 X2))) = (σ (M.op X1 (k X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49689 X0 X1 X2
       have i₂ := eq49834 X1 X0 X2
       grind)
    | exact superpose eq49834 eq49689
    | exact resolve eq49689 eq49834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49689 eq49834
  have eq107602 : ∀ X0 X1 X2 : G, (σ (M.op X2 (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)))) = (M.op (σ X2) (σ (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq107489 (M.op (τ (M.op X0 X0)) X1) X1 (τ X0)
       have i₂ := eq3512 X0 X1
       grind)
    | exact superpose eq3512 eq107489
    | exact resolve eq107489 eq3512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3512 eq107489
  have eq107988 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X1)) = (σ (M.op X2 (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq107602 X0 X1 X2
       have i₂ := eq85269 X1 (σ X2) (τ (M.op X0 X0)) (τ X0)
       grind)
    | exact superpose eq85269 eq107602
    | exact resolve eq107602 eq85269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85269 eq107602
  have eq108109 : ∀ X1 X2 : G, (M.op (σ X2) (σ X1)) = (σ (M.op X2 X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq107988 x X1 X2
       have i₂ := eq25 (τ x) X1 X2 (τ (M.op x x))
       grind)
    | exact superpose eq25 eq107988
    | exact resolve eq107988 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq107988
  have eq108363 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq108109 y x
       grind)
    | exact superpose eq108109 eq16
    | (have r₁ := eq16
       have r₂ := eq108109 y x
       grind)
    | exact resolve eq16 eq108109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108109
  have eq108510 : False := by grind
  exact eq108510

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxx_y_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq50 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq64 : (M.op x y) ≠ (M.op x x) ∨ (k y x) = (M.op y y) := by
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
  have eq65 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op (M.op X2 X1) X0) X0) = (M.op (M.op (M.op X2 X1) X0) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) X0) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X2 X1) X1) X1
       have r₂ := eq14 X1 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq43
    | exact resolve eq43 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq73 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq78 : y ≠ (M.op x y) ∨ (M.op y y) = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq11 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq14 X0 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq14
    | (have j1 := eq11 X1 X0
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq105 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq98 X0 X1 X2
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq98
    | (have j0 := eq98 X0 X1 X2
       grind)
    | exact resolve eq98 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq113 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq114 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq116 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq114
    | exact resolve eq114 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq118 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq116
    | exact resolve eq116 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq116
  have eq124 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq113
       grind)
    | exact superpose eq113 eq16
    | exact resolve eq16 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq118
       grind)
    | exact superpose eq118 eq16
    | exact resolve eq16 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq240 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq238 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq238
    | exact resolve eq238 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq250 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq253 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq250 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq250
    | exact resolve eq250 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq954 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq104 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq1317 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op (M.op X2 X1) X0) X0) = (M.op (M.op (M.op X2 X1) X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X0 X1 X2
       have i₂ := eq54 X0 X1 (M.op (M.op X2 X1) X0) X2
       grind)
    | exact superpose eq54 eq66
    | (have j0 := eq66 X0 X1 X2
       grind)
    | (have r₁ := eq66 (M.op (M.op x X1) X0) X1 X2
       have r₂ := eq54 X0 X1 (M.op (M.op x X1) X0) x
       grind)
    | (have r₁ := eq66 X1 (M.op (M.op x X1) X0) X2
       have r₂ := eq54 X0 X1 X1 x
       grind)
    | exact resolve eq66 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1393 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X1) X1) = (M.op (M.op (M.op X0 X1) X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1317 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317
  have eq4593 : (k (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq1393
    | (have j0 := eq1393 (σ x) (σ y)
       grind)
    | exact resolve eq1393 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq5975 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq954 X0 X1
       have j1 := eq105 X1 X0 x
       grind)
    | (have r₁ := eq954 X0 X1
       have r₂ := eq105 X0 X1 X0
       grind)
    | (have r₁ := eq954 X1 X0
       have r₂ := eq105 X0 X1 X1
       grind)
    | (have r₁ := eq954 X1 (M.op X1 X1)
       have r₂ := eq105 (M.op X1 X1) X1 x
       grind)
    | exact resolve eq954 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq954
  have eq6129 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq5975 x y
       grind)
    | exact superpose eq5975 eq44
    | (have j1 := eq5975 x y
       grind)
    | exact resolve eq44 eq5975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6258 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6129
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6129
    | exact resolve eq6129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6129
  have eq6276 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq6258
    | exact resolve eq6258 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6258
  have eq6286 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6276
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6276
    | exact resolve eq6276 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6276
  have eq6305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6286 eq5975
    | (have j0 := eq5975 (σ x) (σ y)
       grind)
    | exact resolve eq5975 eq6286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6309 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq6305
    | exact resolve eq6305 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6305
  have eq6321 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq6309
       have r₂ := eq27
       grind)
    | exact resolve eq6309 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6309
  have eq6328 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq6321
    | exact resolve eq6321 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6321
  have eq6332 : (k (M.op (σ y) (σ y)) (σ y)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6328 eq4593
    | exact resolve eq4593 eq6328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4593
  have eq6333 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6328 eq79
    | (have r₁ := eq79
       have r₂ := eq6328
       grind)
    | exact resolve eq79 eq6328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq6334 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq6328 eq253
    | exact resolve eq253 eq6328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq6336 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6328 eq27
    | exact resolve eq27 eq6328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6328
  have eq6337 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6333
  have eq6431 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ x)) X1)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq6337 eq54
    | exact resolve eq54 eq6337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6337
  have eq6445 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6431 x X0
       have i₂ := eq54 X0 sF2 x sF3
       grind)
    | exact superpose eq54 eq6431
    | exact resolve eq6431 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6431
  have eq6518 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq6445
    | (have j0 := eq6445 (σ x)
       grind)
    | exact resolve eq6445 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6445
  have eq6571 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6518 eq65
    | (have r₁ := eq65
       have r₂ := eq6518
       grind)
    | exact resolve eq65 eq6518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6597 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6571
  have eq6656 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6597 eq124
    | exact resolve eq124 eq6597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq6597
  have eq6672 : (k y x) = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq150 eq6656
    | exact resolve eq6656 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq6656
  have eq6675 : (M.op y y) = (M.op y x) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq6672
       have i₂ := eq5975 y x
       grind)
    | exact superpose eq5975 eq6672
    | (have j1 := eq5975 x y
       grind)
    | exact resolve eq6672 eq5975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6672
  have eq11035 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 y X0 y
       have i₂ := eq6675
       grind)
    | exact superpose eq6675 eq54
    | exact resolve eq54 eq6675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6675
  have eq11064 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq11035 X0 x
       have i₂ := eq54 x x X0 y
       grind)
    | exact superpose eq54 eq11035
    | exact resolve eq11035 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11035
  have eq12052 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11064 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11064
    | (have j0 := eq11064 x
       grind)
    | exact resolve eq11064 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11064
  have eq12161 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq12052 eq6286
    | exact resolve eq6286 eq12052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12052
  have eq12170 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq12161
  have eq12178 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq12170
       have r₂ := eq6336
       grind)
    | exact resolve eq12170 eq6336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12170
  have eq12196 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq12178
       grind)
    | exact superpose eq12178 eq73
    | exact resolve eq73 eq12178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12178
  have eq12255 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq12196
    | exact resolve eq12196 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12196
  have eq12271 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq12255 eq6518
    | exact resolve eq6518 eq12255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12255
  have eq12309 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq12271
  have eq12315 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq12309
       have r₂ := eq27
       grind)
    | exact resolve eq12309 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12309
  have eq12338 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq12315 eq6286
    | exact resolve eq6286 eq12315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12315
  have eq12347 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq12338
  have eq12355 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12347
       have r₂ := eq6336
       grind)
    | exact resolve eq12347 eq6336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12347
  have eq12370 : x ≠ x ∨ (M.op x y) = (M.op x x) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq12355
       grind)
    | exact superpose eq12355 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12355
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12355
       grind)
    | exact resolve eq12 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12355
  have eq12382 : (M.op x y) = (M.op x x) ∨ x = (k y x) ∨ y = (M.op x y) := by grind
  clear eq12370
  have eq12383 : (M.op x y) = (M.op x x) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12382
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12382
    | exact resolve eq12382 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12382
  have eq12729 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq12383
       grind)
    | exact superpose eq12383 eq73
    | exact resolve eq73 eq12383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12383
  have eq12792 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq12729
    | exact resolve eq12729 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12729
  have eq12841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12792 eq6518
    | exact resolve eq6518 eq12792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6518 eq12792
  have eq12879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y x) := by grind
  clear eq12841
  have eq12885 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq12879
       have r₂ := eq27
       grind)
    | exact resolve eq12879 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12879
  have eq12908 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq12885 eq6286
    | exact resolve eq6286 eq12885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12885
  have eq12917 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k y x) := by grind
  clear eq12908
  have eq12925 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12917
       have r₂ := eq6336
       grind)
    | exact resolve eq12917 eq6336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6336 eq12917
  have eq12945 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq12925
       grind)
    | exact superpose eq12925 eq113
    | exact resolve eq113 eq12925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12925
  have eq12988 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12945
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12945
    | exact resolve eq12945 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12945
  have eq13013 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12988 eq5975
    | (have j0 := eq5975 (σ y) (σ x)
       grind)
    | exact resolve eq5975 eq12988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13018 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq13013
  have eq13070 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13018 eq6334
    | exact resolve eq6334 eq13018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6334 eq13018
  have eq13084 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13070 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13070
  have eq13133 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq13084
    | (have j0 := eq13084 (σ x)
       grind)
    | exact resolve eq13084 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13084
  have eq13336 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13133 eq65
    | (have r₁ := eq65
       have r₂ := eq13133
       grind)
    | exact resolve eq65 eq13133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq13133
  have eq13376 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13336
  have eq13467 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13376 eq12988
    | exact resolve eq12988 eq13376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12988 eq13376
  have eq13471 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13467
  have eq13493 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13471 eq6332
    | exact resolve eq6332 eq13471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6332 eq13471
  have eq13629 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13493
  have eq13672 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq13629
    | exact resolve eq13629 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13629
  have eq13697 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13672 eq6286
    | exact resolve eq6286 eq13672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6286 eq13672
  have eq13708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13697
  have eq13713 : y = (M.op x y) := by
    first
    | (have r₁ := eq13708
       have r₂ := eq27
       grind)
    | exact resolve eq13708 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13708
  have eq13715 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq13713 eq20
    | exact resolve eq20 eq13713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq13719 : y ≠ y ∨ (M.op y y) = (M.op y x) ∨ y = (k x y) := by
    first
    | exact superpose eq13713 eq78
    | (have r₁ := eq78
       have r₂ := eq13713
       grind)
    | exact resolve eq78 eq13713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq13762 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq13713 eq240
    | exact resolve eq240 eq13713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq13772 : (M.op y y) = (M.op y x) ∨ y = (k x y) := by grind
  clear eq13719
  have eq13823 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13715
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13715
    | exact resolve eq13715 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13715
  have eq13838 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq13823 eq26
    | exact resolve eq26 eq13823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq14743 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) ∨ y = (k x y) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 y X0 y
       have i₂ := eq13772
       grind)
    | exact superpose eq13772 eq54
    | exact resolve eq54 eq13772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13772
  have eq14763 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (k x y) := by
    intro X0
    first
    | (have i₁ := eq14743 X0 x
       have i₂ := eq54 x x X0 y
       grind)
    | exact superpose eq54 eq14743
    | exact resolve eq14743 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14743
  have eq14875 : (M.op x y) = (M.op x x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14763 x
       grind)
    | exact superpose eq14763 eq18
    | (have j1 := eq14763 x
       grind)
    | exact resolve eq18 eq14763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq14763
  have eq14930 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq13713 eq14875
    | exact resolve eq14875 eq13713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14875
  have eq14948 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq14930
       grind)
    | exact superpose eq14930 eq44
    | exact resolve eq44 eq14930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq14930
  have eq14976 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq13823 eq14948
    | exact resolve eq14948 eq13823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14948
  have eq14985 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14976
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14976
    | exact resolve eq14976 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14976
  have eq14992 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq13823 eq14985
    | exact resolve eq14985 eq13823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14985
  have eq15005 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14992 eq5975
    | (have j0 := eq5975 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq5975 eq14992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14992
  have eq15010 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq15005
  have eq15014 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq13838 eq15010
    | exact resolve eq15010 eq13838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15010
  have eq15024 : y = (M.op x x) := by
    first
    | (have r₁ := eq15014
       have r₂ := eq27
       grind)
    | exact resolve eq15014 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15014
  have eq15048 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq15024
       grind)
    | exact superpose eq15024 eq64
    | exact resolve eq64 eq15024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq15049 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq15024
       grind)
    | exact superpose eq15024 eq73
    | exact resolve eq73 eq15024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq15076 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 x
       have i₂ := eq15024
       grind)
    | exact superpose eq15024 eq54
    | exact resolve eq54 eq15024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq15024
  have eq15098 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq15076 X0 x
       have i₂ := eq13762 X0 x
       grind)
    | exact superpose eq13762 eq15076
    | exact resolve eq15076 eq13762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13762 eq15076
  have eq15108 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15049
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15049
    | exact resolve eq15049 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq15049
  have eq15109 : (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq15048
       have r₂ := eq13713
       grind)
    | exact resolve eq15048 eq13713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13713 eq15048
  have eq15116 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq13823 eq15108
    | exact resolve eq15108 eq13823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15108
  have eq15245 : (M.op (σ y) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq118
       have i₂ := eq15098 y
       grind)
    | exact superpose eq15098 eq118
    | exact resolve eq118 eq15098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq15298 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y x)) := by
    first
    | exact superpose eq13823 eq15245
    | exact resolve eq15245 eq13823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15245
  have eq15354 : (k y x) = (M.op y x) := by
    first
    | (have i₁ := eq15109
       have i₂ := eq15098 y
       grind)
    | exact superpose eq15098 eq15109
    | exact resolve eq15109 eq15098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15098 eq15109
  have eq15358 : (k (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq15354
       grind)
    | exact superpose eq15354 eq113
    | exact resolve eq113 eq15354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq15354
  have eq15379 : (k (σ (M.op x y)) (σ x)) = (σ (M.op y x)) := by
    first
    | exact superpose eq13823 eq15358
    | exact resolve eq15358 eq13823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13823 eq15358
  have eq15428 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq15379
       have i₂ := eq15298
       grind)
    | exact superpose eq15298 eq15379
    | exact resolve eq15379 eq15298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15298 eq15379
  have eq15429 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq15428
       have i₂ := eq5975 sF1 sF2
       grind)
    | exact superpose eq5975 eq15428
    | (have j1 := eq5975 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq15428 eq5975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17137 : (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq15429 eq13
    | (have j0 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq15429
       grind)
    | exact resolve eq13 eq15429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15429
  have eq17157 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq17137
  have eq17160 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq15116 eq17157
    | exact resolve eq17157 eq15116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17157
  have eq17176 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq17160 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ x)
       have r₂ := eq17160
       grind)
    | exact resolve eq12 eq17160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17177 : (σ x) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq17160 eq13
    | (have j0 := eq13 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq13 eq17160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17160
  have eq17194 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by grind
  clear eq17176
  have eq17196 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq15116 eq17177
    | exact resolve eq17177 eq15116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17177
  have eq17197 : (σ x) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by grind
  clear eq17196
  have eq17198 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq13838 eq17194
    | exact resolve eq17194 eq13838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17194
  have eq17200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq15116 eq17198
    | exact resolve eq17198 eq15116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15116 eq17198
  have eq17201 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq17200
       have r₂ := eq27
       grind)
    | exact resolve eq17200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17200
  have eq17202 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq15428 eq17201
    | exact resolve eq17201 eq15428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15428 eq17201
  have eq17206 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq17202
       have r₂ := eq17197
       grind)
    | exact resolve eq17202 eq17197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17197 eq17202
  have eq17217 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq17206 eq5975
    | (have j0 := eq5975 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq5975 eq17206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5975 eq17206
  have eq17222 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq17217
  have eq17225 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13838 eq17222
    | exact resolve eq17222 eq13838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13838 eq17222
  have eq17234 : False := by grind
  exact eq17234
