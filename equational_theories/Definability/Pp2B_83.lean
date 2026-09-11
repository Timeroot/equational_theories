import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation58`: `x = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation58 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law58 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law58.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq38 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq38 X1 X0
       grind)
    | (have r₁ := eq42 X1 X0
       have r₂ := eq38 X0 X1
       grind)
    | exact resolve eq42 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq42
  have eq47 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq45
  have eq103 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq107 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq103 X0 X1
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq103 X1 X1
       have r₂ := eq47 X1 X1
       grind)
    | exact resolve eq103 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq103
  have eq242 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq107 (σ X0) (σ X1)
       grind)
    | exact superpose eq107 eq15
    | exact resolve eq15 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq242 X0 X1
       have i₂ := eq107 X0 X1
       grind)
    | exact superpose eq107 eq242
    | exact resolve eq242 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq242
  have eq252 : False := by grind
  exact eq252

/-- `Equation58`: `x = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pyx_Equation58 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law58 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law58.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X0))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq27 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq38 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq15
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq10
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq46 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30
    | exact resolve eq30 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X1)
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq19 X0 X0
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq140 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq130 y x
       grind)
    | exact superpose eq130 eq16
    | (have j1 := eq130 y x
       grind)
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) (σ X1)
       have i₂ := eq130 X0 X1
       grind)
    | exact superpose eq130 eq19
    | (have j1 := eq130 X0 X1
       grind)
    | exact resolve eq19 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X2 (σ (k X0 X1)))) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X2 (σ X1)
       have i₂ := eq130 X0 X1
       grind)
    | exact superpose eq130 eq9
    | (have j1 := eq130 X0 X1
       grind)
    | exact resolve eq9 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 X1 X2 : G, (k (σ X2) (k (σ X0) X1)) = (σ (k X2 (M.op (τ X1) X0))) ∨ (M.op X0 X0) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (M.op (τ X1) X0)
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq15
    | (have j1 := eq46 X1 X0
       grind)
    | exact resolve eq15 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq413 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (σ (k X2 (M.op (τ X1) X0))) ∨ (M.op X0 X0) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq399 X0 X1 X2
       have i₂ := eq38 X0 X1 X2
       grind)
    | exact superpose eq38 eq399
    | (have j0 := eq399 X0 X1 X2
       grind)
    | exact resolve eq399 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq399
  have eq420 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq391 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq391
    | (have j0 := eq391 X0 X1
       grind)
    | exact resolve eq391 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq471 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq71 X1
       grind)
    | exact superpose eq71 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq503 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k X1 (σ (M.op X0 (τ X1)))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq471 (M.op X1 (τ X1)) X1
       have i₂ := eq19 (τ X1) X1
       grind)
    | exact superpose eq19 eq471
    | (have j0 := eq471 X0 X1
       grind)
    | exact resolve eq471 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq471
  have eq569 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq140
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq140
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq140
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq140
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq140 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq569
  have eq1030 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (k (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63 (τ X0) (τ X0)
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq63
    | exact resolve eq63 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1033 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (k (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1030 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1036 : ∀ X0 : G, (τ X0) = (τ (k X0 (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1033 X0
       have i₂ := eq49 (M.op X0 X0) X0
       grind)
    | exact superpose eq49 eq1033
    | (have j0 := eq1033 X0
       grind)
    | exact resolve eq1033 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq1263 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (σ X1)
       have i₂ := eq130 X0 X1
       grind)
    | exact superpose eq130 eq78
    | (have j0 := eq78 X0 (σ X1)
       have j1 := eq130 X0 X1
       grind)
    | (have r₁ := eq78 X0 (σ X1)
       have r₂ := eq130 X0 X1
       grind)
    | exact resolve eq78 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq1266 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1263 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq1268 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1266 X0 X1
       have j1 := eq78 X0 (σ X1)
       grind)
    | (have r₁ := eq1266 X0 X1
       have r₂ := eq78 (k X0 X1) (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq1266 X0 X1
       have r₂ := eq78 (M.op X0 X0) (σ (k X0 X1))
       grind)
    | (have r₁ := eq1266 X0 X1
       have r₂ := eq78 X0 (σ X1)
       grind)
    | exact resolve eq1266 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266
  have eq1277 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1268 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1268
    | (have j0 := eq1268 X0 X1
       grind)
    | exact resolve eq1268 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq1484 : ∀ X0 : G, (τ (σ X0)) = (τ (k (σ X0) (σ (M.op X0 X0)))) ∨ (τ (σ X0)) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1036 (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq1036
    | exact resolve eq1036 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1540 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) (M.op X0 X0)) ∨ (τ (σ X0)) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1484 X0
       have i₂ := eq30 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq30 eq1484
    | (have j0 := eq1484 X0
       grind)
    | exact resolve eq1484 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq1544 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ (σ X0)) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1540 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1540
    | (have j0 := eq1540 X0
       grind)
    | exact resolve eq1540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540
  have eq1548 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1544 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1544
    | (have j0 := eq1544 X0
       grind)
    | exact resolve eq1544 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1552 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1548 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1548
    | (have j0 := eq1548 X0
       grind)
    | exact resolve eq1548 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq1644 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1552 (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq1552
    | exact resolve eq1552 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq1682 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1644 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq1644
    | (have j0 := eq1644 X0
       grind)
    | exact resolve eq1644 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq1723 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq143 (τ X1) (τ X0)
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq143
    | (have j0 := eq143 (τ X0) (τ X1)
       grind)
    | exact resolve eq143 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1781 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1723 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1723
    | (have j0 := eq1723 X0 X1
       grind)
    | exact resolve eq1723 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723
  have eq1794 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1781 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1781
    | (have j0 := eq1781 X0 X1
       grind)
    | exact resolve eq1781 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781
  have eq1801 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1794 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1794
    | (have j0 := eq1794 X0 X1
       grind)
    | exact resolve eq1794 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794
  have eq1808 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1801 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1801
    | (have j0 := eq1801 X0 X1
       grind)
    | exact resolve eq1801 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801
  have eq1813 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1808 X0 X1
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq1808
    | (have j0 := eq1808 X0 X1
       grind)
    | exact resolve eq1808 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1808
  have eq1818 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op (k X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1813 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1813
    | (have j0 := eq1813 X0 X1
       grind)
    | exact resolve eq1813 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813
  have eq1823 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1818 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1818
    | (have j0 := eq1818 X0 X1
       grind)
    | exact resolve eq1818 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818
  have eq1842 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op X2 (σ (τ (k X0 X1))))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq145 (τ X0) (τ X1) X2
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq145
    | (have j0 := eq145 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq145 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq1885 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op X2 (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1842 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1842
    | (have j0 := eq1842 X0 X1 X2
       grind)
    | exact resolve eq1842 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842
  have eq1900 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (k X0 X1))) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1885 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1885
    | (have j0 := eq1885 X0 X1 X2
       grind)
    | exact resolve eq1885 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq1908 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 (M.op X2 (k X0 X1))) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1900 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1900
    | (have j0 := eq1900 X0 X1 X2
       grind)
    | exact resolve eq1900 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900
  have eq1915 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 (M.op X2 (k X0 X1))) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1908 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1908
    | (have j0 := eq1908 X0 X1 X2
       grind)
    | exact resolve eq1908 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908
  have eq1921 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 (M.op X2 (k X0 X1))) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1915 X0 X1 X2
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq1915
    | (have j0 := eq1915 X0 X1 X2
       grind)
    | exact resolve eq1915 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1915
  have eq1926 : ∀ X0 X1 X2 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 (M.op X2 (k X0 X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1921 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1921
    | (have j0 := eq1921 X0 X1 X2
       grind)
    | exact resolve eq1921 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq1931 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (k X0 X1))) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1926 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1926
    | (have j0 := eq1926 X0 X1 X2
       grind)
    | exact resolve eq1926 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926
  have eq2535 : ∀ X0 X1 X2 : G, (σ (k X2 (k X1 X0))) = (k (σ X2) (σ (M.op X0 X1))) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X1 X0)
       have i₂ := eq420 X0 X1
       grind)
    | exact superpose eq420 eq15
    | (have j1 := eq420 X0 X1
       grind)
    | exact resolve eq15 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq2574 : ∀ X0 X1 X2 : G, (σ (k X2 (k X1 X0))) = (σ (k X2 (M.op X0 X1))) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2535 X0 X1 X2
       have i₂ := eq15 X2 (M.op X0 X1)
       grind)
    | exact superpose eq15 eq2535
    | (have j0 := eq2535 X0 X1 X2
       grind)
    | exact resolve eq2535 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2535
  have eq2683 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (M.op X0 X0)
       have i₂ := eq1682 X0
       grind)
    | exact superpose eq1682 eq30
    | (have j1 := eq1682 X0
       grind)
    | exact resolve eq30 eq1682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2706 : ∀ X0 X1 : G, (k (τ X1) X0) = (k (τ X1) (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2683 X0 X1
       have i₂ := eq30 X1 X0
       grind)
    | exact superpose eq30 eq2683
    | (have j0 := eq2683 X0 X1
       grind)
    | exact resolve eq2683 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683
  have eq7564 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq570
       grind)
    | exact superpose eq570 eq16
    | exact resolve eq16 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq7565 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7564
       have r₂ := eq24 x
       grind)
    | exact resolve eq7564 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7564
  have eq12051 : ∀ X0 X1 : G, (τ (σ (M.op X0 (τ (σ X1))))) = (k X1 (τ (σ (M.op X0 (τ (σ X1)))))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op X0 (τ (σ X1))) ∨ (τ (σ X1)) = (M.op X0 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 (σ (M.op X0 (τ (σ X1))))
       have i₂ := eq503 X0 (σ X1)
       grind)
    | exact superpose eq503 eq40
    | (have j1 := eq503 X0 (σ X1)
       grind)
    | exact resolve eq40 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq12111 : ∀ X0 X1 : G, (M.op X0 (τ (σ X1))) = (k X1 (M.op X0 (τ (σ X1)))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op X0 (τ (σ X1))) ∨ (τ (σ X1)) = (M.op X0 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12051 X0 X1
       have i₂ := eq10 (M.op X0 (τ (σ X1)))
       grind)
    | exact superpose eq10 eq12051
    | (have j0 := eq12051 X0 X1
       grind)
    | exact resolve eq12051 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12051
  have eq12158 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op X0 (τ (σ X1))) ∨ (τ (σ X1)) = (M.op X0 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12111 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12111
    | (have j0 := eq12111 X0 X1
       grind)
    | exact resolve eq12111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12111
  have eq12193 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (M.op (σ X1) (σ X1))) ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (τ (σ X1)) = (M.op X0 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12158 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq12158
    | (have j0 := eq12158 X0 X1
       grind)
    | exact resolve eq12158 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12158
  have eq12219 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (σ (M.op X1 X1))) ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (τ (σ X1)) = (M.op X0 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12193 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq12193
    | (have j0 := eq12193 X0 X1
       grind)
    | exact resolve eq12193 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12193
  have eq12237 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (τ (σ X1)) = (M.op X0 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12219 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq12219
    | (have j0 := eq12219 X0 X1
       grind)
    | exact resolve eq12219 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12219
  have eq12252 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12237 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12237
    | (have j0 := eq12237 X0 X1
       grind)
    | exact resolve eq12237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12237
  have eq42449 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (M.op X1 X1)) ∨ (σ X1) = (σ (k X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2706 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2706
    | (have j0 := eq2706 X1 X1
       grind)
    | exact resolve eq2706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2706
  have eq42947 : ∀ X0 X1 : G, (k X1 (τ X0)) = (k X1 (τ (M.op X0 X0))) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq42449 X0 (τ X0)
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq42449
    | exact resolve eq42449 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42449
  have eq43139 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op X0 X0)))) ∨ (k X1 (τ X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq42947 X0 X1
       have i₂ := eq20 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq20 eq42947
    | (have j0 := eq42947 X0 X1
       grind)
    | exact resolve eq42947 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42947
  have eq43149 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (k X1 (τ X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq43139 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq43139
    | (have j0 := eq43139 X0 X1
       grind)
    | exact resolve eq43139 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43139
  have eq43158 : ∀ X0 X1 : G, (k X1 (τ X0)) = (k X1 (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43149 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43149
    | (have j0 := eq43149 X0 X1
       grind)
    | exact resolve eq43149 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43149
  have eq43692 : ∀ X0 X1 : G, (σ (k (τ X0) (τ X1))) = (k X0 (σ (τ (M.op X1 X1)))) ∨ (k X1 (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 (τ (M.op X1 X1))
       have i₂ := eq43158 X1 (τ X0)
       grind)
    | exact superpose eq43158 eq20
    | (have j1 := eq43158 X1 X1
       grind)
    | exact resolve eq20 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43158
  have eq43783 : ∀ X0 X1 : G, (σ (k (τ X0) (τ X1))) = (k X0 (M.op X1 X1)) ∨ (k X1 (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43692 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq43692
    | (have j0 := eq43692 X0 X1
       grind)
    | exact resolve eq43692 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43692
  have eq43876 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (k X0 (M.op X1 X1)) ∨ (k X1 (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43783 X0 X1
       have i₂ := eq20 X0 (τ X1)
       grind)
    | exact superpose eq20 eq43783
    | (have j0 := eq43783 X0 X1
       grind)
    | exact resolve eq43783 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43783
  have eq43923 : ∀ X0 X1 : G, (k X1 (M.op X1 X1)) = X1 ∨ (k X0 X1) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43876 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq43876
    | (have j0 := eq43876 X0 X1
       grind)
    | exact resolve eq43876 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43876
  have eq44049 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq43923 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43923
  have eq44052 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44049
  have eq44136 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44052
  have eq44329 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq44136 (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq44136
    | exact resolve eq44136 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44330 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (k (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq44136 (τ X0)
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq44136
    | exact resolve eq44136 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq44136
  have eq44332 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq44330 X0
       have i₂ := eq49 (M.op X0 X0) X0
       grind)
    | exact superpose eq49 eq44330
    | (have j0 := eq44330 X0
       grind)
    | exact resolve eq44330 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44330
  have eq44333 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq44329 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq44329
    | (have j0 := eq44329 X0
       grind)
    | exact resolve eq44329 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44329
  have eq45138 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1277 (τ X1) (τ X0)
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq1277
    | (have j0 := eq1277 (τ X0) (τ (k X0 X1))
       grind)
    | exact resolve eq1277 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277
  have eq45252 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45138 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq45138
    | (have j0 := eq45138 X0 X1
       grind)
    | exact resolve eq45138 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45138
  have eq45312 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45252 X0 X1
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq45252
    | (have j0 := eq45252 X0 X1
       grind)
    | exact resolve eq45252 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq45252
  have eq45356 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45312 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq45312
    | (have j0 := eq45312 X0 X1
       grind)
    | exact resolve eq45312 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45312
  have eq45389 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45356 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45356
    | (have j0 := eq45356 X0 X1
       grind)
    | exact resolve eq45356 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45356
  have eq45403 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq45389 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq45389
    | (have j0 := eq45389 X0 X1
       grind)
    | exact resolve eq45389 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45389
  have eq45415 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45403 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45403
    | (have j0 := eq45403 X0 X1
       grind)
    | exact resolve eq45403 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45403
  have eq45527 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq44333 X0
       have i₂ := eq1682 X0
       grind)
    | exact superpose eq1682 eq44333
    | (have j1 := eq1682 X0
       grind)
    | (have r₁ := eq44333 X0
       have r₂ := eq1682 X0
       grind)
    | exact resolve eq44333 eq1682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682 eq44333
  have eq45536 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq45527 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45527
  have eq45537 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq45536 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45536
  have eq45606 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (M.op X0 X0))
       have i₂ := eq45537 X0
       grind)
    | exact superpose eq45537 eq10
    | exact resolve eq10 eq45537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45764 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq45606 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45606
    | exact resolve eq45606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45606
  have eq108327 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12252 (k X0 X1) X0
       have i₂ := eq1823 X0 X1
       grind)
    | exact superpose eq1823 eq12252
    | (have j0 := eq12252 X1 X0
       have j1 := eq1823 X0 X1
       grind)
    | exact resolve eq12252 eq1823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108779 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq108327 X0 X1
       have j1 := eq45415 X0 X1
       grind)
    | (have r₁ := eq108327 X0 X1
       have r₂ := eq45415 X0 X1
       grind)
    | (have r₁ := eq108327 (k X0 X1) (M.op X0 X0)
       have r₂ := eq45415 X0 X1
       grind)
    | (have r₁ := eq108327 (M.op X0 X0) (k X0 X1)
       have r₂ := eq45415 X0 X1
       grind)
    | exact resolve eq108327 eq45415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45415 eq108327
  have eq108849 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq108779 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq108779 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq108779 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq108779 (M.op X0 X0) (M.op X1 X0)
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq108779 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108779
  have eq109065 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (k X0 (M.op (τ X1) X0))) ∨ (M.op X0 X0) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq413 X0 X1 X0
       have i₂ := eq108849 X0 (τ X1)
       grind)
    | exact superpose eq108849 eq413
    | (have j0 := eq413 X0 X1 x
       have j1 := eq108849 X0 (τ X1)
       grind)
    | exact resolve eq413 eq108849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq109313 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (k X0 (M.op (τ X1) X0))) ∨ (M.op X0 X0) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq109065 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109065
  have eq109472 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (k X0 (M.op (τ X1) X0))) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq109313 X0 X1
       have j1 := eq13 (σ (k X0 (τ X1))) (σ (k X0 (M.op (τ X1) X0)))
       grind)
    | (have r₁ := eq109313 X0 X1
       have r₂ := eq13 X0 (τ X1)
       grind)
    | (have r₁ := eq109313 (τ X1) X1
       have r₂ := eq13 (τ X1) (τ X1)
       grind)
    | exact resolve eq109313 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109313
  have eq109611 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (k X0 (M.op (τ X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq109472 X0 X1
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq109472
    | (have j0 := eq109472 X0 X1
       grind)
    | exact resolve eq109472 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq109472
  have eq167105 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq78 y (σ x)
       have i₂ := eq7565
       grind)
    | exact superpose eq7565 eq78
    | (have j0 := eq78 x (σ y)
       grind)
    | (have r₁ := eq78 y (σ x)
       have r₂ := eq7565
       grind)
    | exact resolve eq78 eq7565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq7565
  have eq167166 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq167105
  have eq167167 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq167166
  have eq167177 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq167167
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq167167
    | exact resolve eq167167 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167167
  have eq167905 : (σ x) = (σ y) ∨ (σ y) = (σ (k y (M.op x y))) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq45537 y
       have i₂ := eq167177
       grind)
    | exact superpose eq167177 eq45537
    | exact resolve eq45537 eq167177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167177
  have eq169487 : y = (τ (σ x)) ∨ (σ y) = (σ (k y (M.op x y))) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq167905
       grind)
    | exact superpose eq167905 eq10
    | exact resolve eq10 eq167905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167905
  have eq169909 : x = y ∨ (σ y) = (σ (k y (M.op x y))) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq169487
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq169487
    | exact resolve eq169487 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169487
  have eq170552 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y (M.op x y))) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq169909
       grind)
    | exact superpose eq169909 eq16
    | exact resolve eq16 eq169909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169909
  have eq170553 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (k y (M.op x y))) := by
    first
    | (have r₁ := eq170552
       have r₂ := eq24 x
       grind)
    | exact resolve eq170552 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170552
  have eq170574 : ∀ X0 : G, (σ (k (k y x) X0)) = (k (σ y) (σ X0)) ∨ (σ y) = (σ (k y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y x) X0
       have i₂ := eq170553
       grind)
    | exact superpose eq170553 eq15
    | exact resolve eq15 eq170553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170581 : ∀ X0 : G, (τ (k X0 (σ y))) = (k (τ X0) (k y x)) ∨ (σ y) = (σ (k y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq30 X0 (k y x)
       have i₂ := eq170553
       grind)
    | exact superpose eq170553 eq30
    | exact resolve eq30 eq170553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170553
  have eq170988 : ∀ X0 : G, (k (τ X0) y) = (k (τ X0) (k y x)) ∨ (σ y) = (σ (k y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq170581 X0
       have i₂ := eq30 X0 y
       grind)
    | exact superpose eq30 eq170581
    | exact resolve eq170581 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170581
  have eq170995 : ∀ X0 : G, (σ y) = (σ (k y (M.op x y))) ∨ (σ (k (k y x) X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq170574 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq170574
    | exact resolve eq170574 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170574
  have eq174439 : ∀ X0 : G, (k X0 (k y x)) = (k X0 y) ∨ (σ y) = (σ (k y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq170988 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq170988
    | exact resolve eq170988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170988
  have eq234941 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (k (σ X1) (σ X0)) = (σ (k X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq109611 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq109611
    | exact resolve eq109611 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109611
  have eq235690 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (σ (k X1 X0)) = (σ (k X1 (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq234941 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq234941
    | (have j0 := eq234941 X0 X1
       grind)
    | exact resolve eq234941 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234941
  have eq236906 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = (σ (k (τ X0) (M.op X1 (τ X0)))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq235690 X1 (τ X0)
       grind)
    | exact superpose eq235690 eq20
    | (have j1 := eq235690 X1 (τ X0)
       grind)
    | exact resolve eq20 eq235690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235690
  have eq237311 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ (k (τ X0) X1)) = (σ (k (τ X0) (M.op X1 (τ X0)))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq236906 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq236906
    | (have j0 := eq236906 X0 X1
       grind)
    | exact resolve eq236906 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236906
  have eq237598 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ (M.op X1 (τ X0)))) ∨ (k X0 (σ X1)) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq237311 X0 X1
       have i₂ := eq20 X0 (M.op X1 (τ X0))
       grind)
    | exact superpose eq20 eq237311
    | (have j0 := eq237311 X0 X1
       grind)
    | exact resolve eq237311 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237311
  have eq237725 : ∀ X0 X1 : G, (k X0 (σ X1)) = (k X0 (σ (M.op X1 (τ X0)))) ∨ (k X0 (σ X1)) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq237598 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq237598
    | (have j0 := eq237598 X0 X1
       grind)
    | exact resolve eq237598 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq237598
  have eq316118 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X1))) = (k X0 (τ (σ (M.op X1 (τ (σ X0)))))) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 (σ (M.op X1 (τ (σ X0))))
       have i₂ := eq237725 (σ X0) X1
       grind)
    | exact superpose eq237725 eq40
    | (have j1 := eq237725 (σ X0) X1
       grind)
    | exact resolve eq40 eq237725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq237725
  have eq316592 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X1))) = (k X0 (M.op X1 (τ (σ X0)))) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq316118 X0 X1
       have i₂ := eq10 (M.op X1 (τ (σ X0)))
       grind)
    | exact superpose eq10 eq316118
    | (have j0 := eq316118 X0 X1
       grind)
    | exact resolve eq316118 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316118
  have eq316804 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X1))) = (k X0 (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq316592 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq316592
    | (have j0 := eq316592 X0 X1
       grind)
    | exact resolve eq316592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316592
  have eq316991 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (k X0 (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq316804 X0 X1
       have i₂ := eq30 (σ X0) X1
       grind)
    | exact superpose eq30 eq316804
    | (have j0 := eq316804 X0 X1
       grind)
    | exact resolve eq316804 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq316804
  have eq317149 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq316991 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq316991
    | (have j0 := eq316991 X0 X1
       grind)
    | exact resolve eq316991 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316991
  have eq317284 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (k X0 (M.op X1 X0)) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq317149 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq317149
    | (have j0 := eq317149 X0 X1
       grind)
    | exact resolve eq317149 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317149
  have eq317391 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq317284 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq317284
    | (have j0 := eq317284 X0 X1
       grind)
    | exact resolve eq317284 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317284
  have eq318151 : ∀ X0 : G, (σ y) = (σ (k y x)) ∨ (σ (k (k y x) X0)) = (σ (k y X0)) ∨ (σ y) = (σ (k y x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq170995 X0
       have i₂ := eq317391 y x
       grind)
    | exact superpose eq317391 eq170995
    | (have j0 := eq170995 X0
       have j1 := eq317391 y x
       grind)
    | exact resolve eq170995 eq317391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170995
  have eq318157 : ∀ X0 : G, x = y ∨ (σ (k (k y x) X0)) = (σ (k y X0)) ∨ (σ y) = (σ (k y x)) := by
    intro X0
    first
    | (have j0 := eq318151 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318151
  have eq320626 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k (k y x) X0)) = (σ (k y X0)) ∨ (σ y) = (σ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq318157 X0
       grind)
    | exact superpose eq318157 eq16
    | (have j1 := eq318157 X0
       grind)
    | exact resolve eq16 eq318157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318157
  have eq320654 : ∀ X0 : G, (σ y) = (σ (k y x)) ∨ (σ (k (k y x) X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have j0 := eq320626 X0
       grind)
    | (have r₁ := eq320626 X0
       have r₂ := eq24 x
       grind)
    | exact resolve eq320626 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320626
  have eq320703 : ∀ X0 X1 : G, (σ (k (k y x) X0)) = (k (σ y) (σ X0)) ∨ (σ (k y X1)) = (σ (k (k y x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k y x) X0
       have i₂ := eq320654 X1
       grind)
    | exact superpose eq320654 eq15
    | (have j1 := eq320654 X1
       grind)
    | exact resolve eq15 eq320654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320654
  have eq321262 : ∀ X0 X1 : G, (σ (k (k y x) X0)) = (σ (k y X0)) ∨ (σ (k y X1)) = (σ (k (k y x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq320703 X0 X1
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq320703
    | (have j0 := eq320703 X0 X0
       grind)
    | exact resolve eq320703 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320703
  have eq420677 : ∀ X0 : G, (σ (k y X0)) ≠ (σ (k y X0)) ∨ (σ (k (k y x) X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have j0 := eq321262 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321262
  have eq420678 : ∀ X0 : G, (σ (k (k y x) X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have j0 := eq420677 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420677
  have eq423144 : ∀ X0 : G, (k (k y x) X0) = (τ (σ (k y X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k (k y x) X0)
       have i₂ := eq420678 X0
       grind)
    | exact superpose eq420678 eq10
    | exact resolve eq10 eq420678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420678
  have eq423734 : ∀ X0 : G, (k (k y x) X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq423144 X0
       have i₂ := eq10 (k y X0)
       grind)
    | exact superpose eq10 eq423144
    | exact resolve eq423144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423144
  have eq423835 : ∀ X0 : G, x = y ∨ (M.op x y) = (M.op y y) ∨ (k y X0) = (k (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq423734 X0
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq423734
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq423734 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423841 : (M.op (k y x) (k y x)) = (k y (k y x)) := by grind
  clear eq423734
  have eq435943 : y = (M.op y (k y (k y x))) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1931 y x (k y x)
       have i₂ := eq423841
       grind)
    | exact superpose eq423841 eq1931
    | (have j0 := eq1931 y x x
       grind)
    | exact resolve eq1931 eq423841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423841
  have eq479712 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (k y X0) = (k (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq423835 X0
       grind)
    | exact superpose eq423835 eq16
    | (have j1 := eq423835 X0
       grind)
    | exact resolve eq16 eq423835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423835
  have eq479821 : ∀ X0 : G, (M.op x y) = (M.op y y) ∨ (k y X0) = (k (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq479712 X0
       grind)
    | (have r₁ := eq479712 X0
       have r₂ := eq24 x
       grind)
    | exact resolve eq479712 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479712
  have eq480965 : ∀ X0 : G, (k y X0) = (k (M.op x y) X0) ∨ (σ y) = (σ (k y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq45537 y
       have i₂ := eq479821 X0
       grind)
    | exact superpose eq479821 eq45537
    | (have j1 := eq479821 X0
       grind)
    | exact resolve eq45537 eq479821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479821
  have eq485205 : (k y (k y x)) = (k (M.op x y) y) ∨ (σ y) = (σ (k y (M.op x y))) ∨ (σ y) = (σ (k y (M.op x y))) := by
    first
    | (have i₁ := eq174439 (M.op x y)
       have i₂ := eq480965 (k y x)
       grind)
    | exact superpose eq480965 eq174439
    | exact resolve eq174439 eq480965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174439
  have eq485206 : (k y (k y x)) = (k (M.op x y) y) ∨ (σ y) = (σ (k y (M.op x y))) := by grind
  clear eq485205
  have eq485319 : y = (M.op y (k y x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq435943
       have i₂ := eq108849 y x
       grind)
    | exact superpose eq108849 eq435943
    | (have j1 := eq108849 y x
       grind)
    | exact resolve eq435943 eq108849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108849 eq435943
  have eq485391 : y = (M.op y (k y x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (k y x) := by grind
  clear eq485319
  have eq485403 : y = (M.op y (k y x)) ∨ x = y ∨ y = (k y x) := by
    first
    | (have j1 := eq13 y (M.op y (k y x))
       grind)
    | (have r₁ := eq485391
       have r₂ := eq13 y x
       grind)
    | exact resolve eq485391 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485391
  have eq485419 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq1931 y x y
       have i₂ := eq485403
       grind)
    | exact superpose eq485403 eq1931
    | (have j0 := eq1931 y x x
       grind)
    | exact resolve eq1931 eq485403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931 eq485403
  have eq485490 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (k y x) := by grind
  clear eq485419
  have eq485514 : x = y ∨ y = (M.op y y) ∨ y = (k y x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq485490
       have r₂ := eq13 y x
       grind)
    | exact resolve eq485490 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485490
  have eq485547 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq485514
       grind)
    | exact superpose eq485514 eq16
    | exact resolve eq16 eq485514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485514
  have eq485660 : y = (k y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq485547
       have r₂ := eq24 x
       grind)
    | exact resolve eq485547 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485547
  have eq485738 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1823 y x
       have i₂ := eq485660
       grind)
    | exact superpose eq485660 eq1823
    | (have j0 := eq1823 y x
       grind)
    | exact resolve eq1823 eq485660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823 eq485660
  have eq485785 : x = y ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq485738
  have eq487451 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq485785
       grind)
    | exact superpose eq485785 eq16
    | exact resolve eq16 eq485785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485785
  have eq487569 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq487451
       have r₂ := eq24 x
       grind)
    | exact resolve eq487451 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487451
  have eq487689 : (τ y) ≠ (τ y) ∨ (τ y) = (τ (k y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq44332 y
       have i₂ := eq487569
       grind)
    | exact superpose eq487569 eq44332
    | exact resolve eq44332 eq487569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44332
  have eq487745 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq487569
  have eq487747 : (τ y) = (τ (k y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq487689
  have eq487752 : (M.op x y) = (M.op y y) ∨ (τ y) = (τ (M.op y y)) := by grind
  clear eq487747
  have eq489700 : (τ y) = (τ (M.op y y)) ∨ (σ y) = (σ (k y (M.op x y))) := by
    first
    | (have i₁ := eq45537 y
       have i₂ := eq487752
       grind)
    | exact superpose eq487752 eq45537
    | exact resolve eq45537 eq487752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487752
  have eq497359 : ∀ X0 : G, (τ (k X0 (M.op y y))) = (k (τ X0) (τ y)) ∨ (σ y) = (σ (k y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq49 (M.op y y) X0
       have i₂ := eq489700
       grind)
    | exact superpose eq489700 eq49
    | exact resolve eq49 eq489700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489700
  have eq497870 : ∀ X0 : G, (τ (k X0 y)) = (τ (k X0 (M.op y y))) ∨ (σ y) = (σ (k y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq497359 X0
       have i₂ := eq49 y X0
       grind)
    | exact superpose eq49 eq497359
    | exact resolve eq497359 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq497359
  have eq750810 : ∀ X0 : G, (k X0 (M.op y y)) = (σ (τ (k X0 y))) ∨ (σ y) = (σ (k y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 (M.op y y))
       have i₂ := eq497870 X0
       grind)
    | exact superpose eq497870 eq11
    | exact resolve eq11 eq497870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497870
  have eq751432 : ∀ X0 : G, (k X0 y) = (k X0 (M.op y y)) ∨ (σ y) = (σ (k y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq750810 X0
       have i₂ := eq11 (k X0 y)
       grind)
    | exact superpose eq11 eq750810
    | exact resolve eq750810 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750810
  have eq753210 : (k y (M.op y y)) = (k (M.op x y) y) ∨ (σ y) = (σ (k y (M.op x y))) ∨ (σ y) = (σ (k y (M.op x y))) := by
    first
    | (have i₁ := eq480965 (M.op y y)
       have i₂ := eq751432 (M.op x y)
       grind)
    | exact superpose eq751432 eq480965
    | exact resolve eq480965 eq751432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480965 eq751432
  have eq753643 : (k y (M.op y y)) = (k (M.op x y) y) ∨ (σ y) = (σ (k y (M.op x y))) := by grind
  clear eq753210
  have eq753747 : y = (k (M.op x y) y) ∨ (σ y) = (σ (k y (M.op x y))) := by
    first
    | (have i₁ := eq753643
       have i₂ := eq45764 y
       grind)
    | exact superpose eq45764 eq753643
    | exact resolve eq753643 eq45764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45764 eq753643
  have eq755208 : y = (k y (k y x)) ∨ (σ y) = (σ (k y (M.op x y))) ∨ (σ y) = (σ (k y (M.op x y))) := by
    first
    | (have i₁ := eq485206
       have i₂ := eq753747
       grind)
    | exact superpose eq753747 eq485206
    | exact resolve eq485206 eq753747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485206 eq753747
  have eq755328 : y = (k y (k y x)) ∨ (σ y) = (σ (k y (M.op x y))) := by grind
  clear eq755208
  have eq757550 : (σ y) = (σ (k y (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (σ (k y (M.op x y))) := by
    first
    | (have i₁ := eq2574 x y y
       have i₂ := eq755328
       grind)
    | exact superpose eq755328 eq2574
    | (have j0 := eq2574 x y x
       grind)
    | exact resolve eq2574 eq755328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574 eq755328
  have eq757625 : x = y ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (σ (k y (M.op x y))) := by grind
  clear eq757550
  have eq766224 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (σ (k y (M.op x y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq757625
       grind)
    | exact superpose eq757625 eq16
    | exact resolve eq16 eq757625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757625
  have eq766527 : (M.op x y) = (M.op y y) ∨ (σ y) = (σ (k y (M.op x y))) := by
    first
    | (have r₁ := eq766224
       have r₂ := eq24 x
       grind)
    | exact resolve eq766224 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766224
  have eq766811 : (σ y) = (σ (k y (M.op x y))) ∨ (σ y) = (σ (k y (M.op x y))) := by
    first
    | (have i₁ := eq45537 y
       have i₂ := eq766527
       grind)
    | exact superpose eq766527 eq45537
    | exact resolve eq45537 eq766527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45537 eq766527
  have eq766879 : (σ y) = (σ (k y (M.op x y))) := by grind
  clear eq766811
  have eq766946 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq766879
       have i₂ := eq317391 y x
       grind)
    | exact superpose eq317391 eq766879
    | (have j1 := eq317391 y x
       grind)
    | exact resolve eq766879 eq317391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317391
  have eq766989 : (τ (σ y)) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq10 (k y (M.op x y))
       have i₂ := eq766879
       grind)
    | exact superpose eq766879 eq10
    | exact resolve eq10 eq766879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766879
  have eq767628 : x = y ∨ (σ y) = (σ (k y x)) := by grind
  clear eq766946
  have eq767702 : y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq766989
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq766989
    | exact resolve eq766989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766989
  have eq767772 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12252 x y
       have i₂ := eq767702
       grind)
    | exact superpose eq767702 eq12252
    | (have j0 := eq12252 x y
       grind)
    | exact resolve eq12252 eq767702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12252 eq767702
  have eq767855 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq767772
  have eq767902 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq767855
       have r₂ := eq487745
       grind)
    | exact resolve eq767855 eq487745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487745 eq767855
  have eq772584 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq767628
       grind)
    | exact superpose eq767628 eq16
    | exact resolve eq16 eq767628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767628
  have eq772889 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq772584
       have r₂ := eq24 x
       grind)
    | exact resolve eq772584 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772584
  have eq772992 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq140
       have i₂ := eq772889
       grind)
    | exact superpose eq772889 eq140
    | exact resolve eq140 eq772889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq772998 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq143 y x
       have i₂ := eq772889
       grind)
    | exact superpose eq772889 eq143
    | (have j0 := eq143 y x
       grind)
    | exact resolve eq143 eq772889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq772889
  have eq774119 : (σ y) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq772998
       have i₂ := eq24 y
       grind)
    | exact superpose eq24 eq772998
    | exact resolve eq772998 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772998
  have eq774122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq772992
       have i₂ := eq767902
       grind)
    | exact superpose eq767902 eq772992
    | exact resolve eq772992 eq767902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772992
  have eq774331 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq774119
       have i₂ := eq767902
       grind)
    | exact superpose eq767902 eq774119
    | exact resolve eq774119 eq767902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774119
  have eq774334 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq774122
       have r₂ := eq16
       grind)
    | exact resolve eq774122 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774122
  have eq774374 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq774331
       have i₂ := eq767902
       grind)
    | exact superpose eq767902 eq774331
    | exact resolve eq774331 eq767902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767902 eq774331
  have eq774385 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq774374
       have r₂ := eq16
       grind)
    | exact resolve eq774374 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774374
  have eq776728 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq774385
       have r₂ := eq774334
       grind)
    | exact resolve eq774385 eq774334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774334 eq774385
  have eq776745 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq776728
       grind)
    | exact superpose eq776728 eq10
    | exact resolve eq10 eq776728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776728
  have eq777692 : x = y := by
    first
    | (have i₁ := eq776745
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq776745
    | exact resolve eq776745 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776745
  have eq779065 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq777692
       grind)
    | exact superpose eq777692 eq16
    | exact resolve eq16 eq777692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777692
  have eq779378 : False := by grind
  exact eq779378

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyy_pyy_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
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
  clear eq19
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq63 (τ X0)
       grind)
    | exact superpose eq63 eq32
    | exact resolve eq32 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq68
    | exact resolve eq68 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq66
  have eq91 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq12
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (k X1 (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (τ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq12
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq407 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
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
  clear eq29
  have eq410 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
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
  have eq419 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq402
    | (have j0 := eq402 X0 X1
       grind)
    | exact resolve eq402 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq700 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq419 x y
       grind)
    | exact superpose eq419 eq16
    | (have j1 := eq419 x y
       grind)
    | exact resolve eq16 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq419 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq3150 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq410 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq410
    | exact resolve eq410 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq3207 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3150 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3150
    | (have j0 := eq3150 X0 X1
       grind)
    | exact resolve eq3150 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3150
  have eq3420 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq407 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq407
    | exact resolve eq407 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq3517 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3420 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq3420
    | (have j0 := eq3420 X0 X1
       grind)
    | exact resolve eq3420 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3420
  have eq3868 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq700
       have i₂ := eq3207 x y
       grind)
    | exact superpose eq3207 eq700
    | (have j1 := eq3207 x y
       grind)
    | (have r₁ := eq700
       have r₂ := eq3207 x y
       grind)
    | (have r₁ := eq700
       have r₂ := eq3207 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq700
       have r₂ := eq3207 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq700 eq3207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3207
  have eq3869 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq3868
  have eq6860 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq706 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq706
    | (have j0 := eq706 (τ X0) (τ X1)
       grind)
    | exact resolve eq706 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq6925 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X1 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6860 X0 X1
       have i₂ := eq75 X1
       grind)
    | exact superpose eq75 eq6860
    | (have j0 := eq6860 X0 X1
       grind)
    | exact resolve eq6860 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6860
  have eq6959 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6925 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq6925
    | (have j0 := eq6925 X0 X1
       grind)
    | exact resolve eq6925 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6925
  have eq6988 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6959 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6959
    | (have j0 := eq6959 X0 X1
       grind)
    | exact resolve eq6959 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6959
  have eq7013 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6988 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6988
    | (have j0 := eq6988 X0 X1
       grind)
    | exact resolve eq6988 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6988
  have eq7034 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (σ (τ (M.op X1 X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7013 X0 X1
       have i₂ := eq75 X1
       grind)
    | exact superpose eq75 eq7013
    | (have j0 := eq7013 X0 X1
       grind)
    | exact resolve eq7013 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7013
  have eq7054 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7034 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq7034
    | (have j0 := eq7034 X0 X1
       grind)
    | exact resolve eq7034 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7034
  have eq7069 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7054 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7054
    | (have j0 := eq7054 X0 X1
       grind)
    | exact resolve eq7054 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7054
  have eq7083 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7069 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7069
    | (have j0 := eq7069 X0 X1
       grind)
    | exact resolve eq7069 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7069
  have eq7092 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7083 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7083
    | (have j0 := eq7083 X0 X1
       grind)
    | exact resolve eq7083 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7083
  have eq7122 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (M.op (τ X1) (τ X1)) ∨ (M.op (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7092 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq7092
    | (have j0 := eq7092 (τ X0) (τ X1)
       grind)
    | exact resolve eq7092 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7092
  have eq7151 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (τ (M.op X1 X1)) ∨ (M.op (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7122 X0 X1
       have i₂ := eq75 X1
       grind)
    | exact superpose eq75 eq7122
    | (have j0 := eq7122 X0 X1
       grind)
    | exact resolve eq7122 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7122
  have eq7165 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (τ (M.op X1 X1)) ∨ (τ (M.op X1 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7151 X0 X1
       have i₂ := eq75 X1
       grind)
    | exact superpose eq75 eq7151
    | (have j0 := eq7151 X0 X1
       grind)
    | exact resolve eq7151 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq7151
  have eq14540 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3869
       grind)
    | exact superpose eq3869 eq16
    | exact resolve eq16 eq3869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3869
  have eq14541 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq14540
       have r₂ := eq77 x
       grind)
    | exact resolve eq14540 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14540
  have eq14545 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq91 y (σ x)
       have i₂ := eq14541
       grind)
    | exact superpose eq14541 eq91
    | (have j0 := eq91 y (σ x)
       grind)
    | (have r₁ := eq91 y (σ x)
       have r₂ := eq14541
       grind)
    | exact resolve eq91 eq14541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14541
  have eq14546 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq14545
  have eq14549 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq14546
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq14546
    | exact resolve eq14546 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14546
  have eq14551 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k X0 y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq14549
       grind)
    | exact superpose eq14549 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq14549
       grind)
    | exact resolve eq12 eq14549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14549
  have eq190692 : (σ x) = (σ y) ∨ (M.op x y) = (k x y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have j0 := eq14551 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14551
  have eq190721 : y = (τ (σ x)) ∨ (M.op x y) = (k x y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq190692
       grind)
    | exact superpose eq190692 eq10
    | exact resolve eq10 eq190692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190692
  have eq190947 : x = y ∨ (M.op x y) = (k x y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq190721
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq190721
    | exact resolve eq190721 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190721
  have eq190949 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq190947
       grind)
    | exact superpose eq190947 eq16
    | exact resolve eq16 eq190947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190947
  have eq190950 : (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq190949
       have r₂ := eq77 x
       grind)
    | exact resolve eq190949 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190949
  have eq190991 : (k x y) = (τ (σ (M.op y y))) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq190950
       grind)
    | exact superpose eq190950 eq10
    | exact resolve eq10 eq190950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190950
  have eq191218 : (k x y) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq190991
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq190991
    | exact resolve eq190991 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190991
  have eq191273 : (τ (M.op y y)) ≠ (τ (M.op y y)) ∨ (τ (M.op y y)) = (M.op (τ x) (τ y)) ∨ (τ y) = (τ x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq7165 x y
       have i₂ := eq191218
       grind)
    | exact superpose eq191218 eq7165
    | (have j0 := eq7165 x y
       grind)
    | exact resolve eq7165 eq191218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7165
  have eq191338 : (M.op x y) ≠ (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq191218
  have eq191339 : (τ (M.op y y)) = (M.op (τ x) (τ y)) ∨ (τ y) = (τ x) ∨ (M.op x y) = (k x y) := by grind
  clear eq191273
  have eq192616 : (τ (M.op y y)) ≠ (τ (M.op y y)) ∨ (τ (M.op y y)) = (k (τ x) (τ y)) ∨ (τ y) = (τ x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq100 y (τ x)
       have i₂ := eq191339
       grind)
    | exact superpose eq191339 eq100
    | (have j0 := eq100 y (τ x)
       grind)
    | (have r₁ := eq100 y (τ x)
       have r₂ := eq191339
       grind)
    | exact resolve eq100 eq191339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq191339
  have eq192651 : (τ (M.op y y)) = (k (τ x) (τ y)) ∨ (τ y) = (τ x) ∨ (M.op x y) = (k x y) := by grind
  clear eq192616
  have eq192666 : (τ y) = (τ x) ∨ (τ (M.op y y)) = (τ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq192651
       have i₂ := eq32 y x
       grind)
    | exact superpose eq32 eq192651
    | exact resolve eq192651 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq192651
  have eq192707 : y = (σ (τ x)) ∨ (τ (M.op y y)) = (τ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq11 y
       have i₂ := eq192666
       grind)
    | exact superpose eq192666 eq11
    | exact resolve eq11 eq192666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192666
  have eq192900 : x = y ∨ (τ (M.op y y)) = (τ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq192707
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq192707
    | exact resolve eq192707 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192707
  have eq192901 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (τ (M.op y y)) = (τ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq192900
       grind)
    | exact superpose eq192900 eq16
    | exact resolve eq16 eq192900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192900
  have eq192911 : (τ (M.op y y)) = (τ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq192901
       have r₂ := eq77 x
       grind)
    | exact resolve eq192901 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192901
  have eq192915 : (τ (M.op y y)) = (τ (M.op x y)) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq192911
       have i₂ := eq3517 x y
       grind)
    | exact superpose eq3517 eq192911
    | (have j1 := eq3517 x y
       grind)
    | exact resolve eq192911 eq3517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3517 eq192911
  have eq193146 : x = y ∨ (M.op x y) = (k x y) ∨ (τ (M.op y y)) = (τ (M.op x y)) := by
    first
    | (have r₁ := eq192915
       have r₂ := eq191338
       grind)
    | exact resolve eq192915 eq191338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192915
  have eq193147 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) ∨ (τ (M.op y y)) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq193146
       grind)
    | exact superpose eq193146 eq16
    | exact resolve eq16 eq193146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193146
  have eq193158 : (τ (M.op y y)) = (τ (M.op x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq193147
       have r₂ := eq77 x
       grind)
    | exact resolve eq193147 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193147
  have eq193204 : (M.op y y) = (σ (τ (M.op x y))) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq11 (M.op y y)
       have i₂ := eq193158
       grind)
    | exact superpose eq193158 eq11
    | exact resolve eq11 eq193158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193158
  have eq193397 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq193204
       have i₂ := eq11 (M.op x y)
       grind)
    | exact superpose eq11 eq193204
    | exact resolve eq193204 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193204
  have eq193398 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq193397
       have r₂ := eq191338
       grind)
    | exact resolve eq193397 eq191338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191338 eq193397
  have eq193404 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq700
       have i₂ := eq193398
       grind)
    | exact superpose eq193398 eq700
    | exact resolve eq700 eq193398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq193420 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq193404
  have eq193422 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq193420
       grind)
    | exact superpose eq193420 eq16
    | exact resolve eq16 eq193420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193436 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq91 y (σ x)
       have i₂ := eq193420
       grind)
    | exact superpose eq193420 eq91
    | (have j0 := eq91 y (σ x)
       grind)
    | (have r₁ := eq91 y (σ x)
       have r₂ := eq193420
       grind)
    | exact resolve eq91 eq193420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq193420
  have eq193471 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq193436
  have eq193494 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq193471
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq193471
    | exact resolve eq193471 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193471
  have eq193509 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq193494
       have i₂ := eq193398
       grind)
    | exact superpose eq193398 eq193494
    | exact resolve eq193494 eq193398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193398 eq193494
  have eq193524 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq193509
       have r₂ := eq193422
       grind)
    | exact resolve eq193509 eq193422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193422 eq193509
  have eq193539 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq193524
       grind)
    | exact superpose eq193524 eq16
    | exact resolve eq16 eq193524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193540 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq193524
       grind)
    | exact superpose eq193524 eq10
    | exact resolve eq10 eq193524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193524
  have eq193769 : x = y := by
    first
    | (have i₁ := eq193540
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq193540
    | exact resolve eq193540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193540
  have eq193770 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq193539
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq193539
    | exact resolve eq193539 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq193539
  have eq193771 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq193770
       have i₂ := eq193769
       grind)
    | exact superpose eq193769 eq193770
    | exact resolve eq193770 eq193769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193769 eq193770
  have eq193772 : False := by grind
  exact eq193772

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_x_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X0 X0) X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq18
    | exact resolve eq18 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq38
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq38
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq56 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op (M.op X0 X0) X1))) = X0 ∨ (M.op (M.op X1 (M.op (M.op X0 X0) X1)) X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X1)) (M.op X1 (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op (M.op X0 X0) X1))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op (M.op X0 X0) X1))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op (M.op X0 X0) X1))
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op X0 X0) X1)) X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X1)) (M.op X1 (M.op (M.op X0 X0) X1))) ∨ (k X0 (M.op X1 (M.op (M.op X0 X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq60 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq29
    | exact resolve eq29 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq219 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq89 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq247 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq219 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq219
    | (have j0 := eq219 X0 X1
       grind)
    | exact resolve eq219 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq219
  have eq253 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq247 X0 X1
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq247 X1 X0
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq247 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq247
  have eq329 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X1) ≠ (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X2) ∨ (k X2 (M.op X0 (M.op (M.op X1 X1) X0))) = (M.op X2 (M.op X0 (M.op (M.op X1 X1) X0))) ∨ (k X1 (M.op X0 (M.op (M.op X1 X1) X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq12
    | (have j0 := eq12 X2 (M.op X0 (M.op (M.op X1 X1) X0))
       have j1 := eq57 X1 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op (M.op X0 X0) X1))
       have r₂ := eq57 X0 X1
       grind)
    | exact resolve eq12 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq386 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq253 (σ X0) X1
       grind)
    | exact superpose eq253 eq15
    | (have j1 := eq253 (σ X0) X1
       grind)
    | exact resolve eq15 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq1399 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (M.op (σ X2) (k (σ X0) X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (σ X0) X1) (σ X2)
       have i₂ := eq221 X0 X1 X2
       grind)
    | exact superpose eq221 eq13
    | (have j0 := eq13 (k (σ X0) X1) (σ X2)
       have j1 := eq221 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq221 X0 X1 X2
       grind)
    | exact resolve eq13 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq1401 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (M.op (σ X2) (k (σ X0) X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1399 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1403 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (k (k X0 (τ X1)) X2)) ∨ (M.op (σ X2) (k (σ X0) X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1401 X0 X1 X2
       have i₂ := eq28 X0 X1 X2
       grind)
    | exact superpose eq28 eq1401
    | (have j0 := eq1401 X0 X1 X2
       grind)
    | exact resolve eq1401 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1401
  have eq1419 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ (k (k X0 (τ X1)) X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1403 X0 X1 X2
       have i₂ := eq40 X2
       grind)
    | exact superpose eq40 eq1403
    | (have j0 := eq1403 X0 X1 X2
       grind)
    | exact resolve eq1403 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403
  have eq1420 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (k (k X0 (τ X1)) X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1419 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419
  have eq1533 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq386 x y
       grind)
    | exact superpose eq386 eq16
    | (have j1 := eq386 x y
       grind)
    | exact resolve eq16 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1556 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq386 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq1601 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1556 (τ X0) (τ X1)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq1556
    | (have j0 := eq1556 (τ X0) (τ X1)
       grind)
    | exact resolve eq1556 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1611 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1601 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1601
    | (have j0 := eq1601 X0 X1
       grind)
    | exact resolve eq1601 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq1614 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1611 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1611
    | (have j0 := eq1611 X0 X1
       grind)
    | exact resolve eq1611 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1611
  have eq1615 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1614 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1614
    | (have j0 := eq1614 X0 X1
       grind)
    | exact resolve eq1614 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614
  have eq1616 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1615 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1615
    | (have j0 := eq1615 X0 X1
       grind)
    | exact resolve eq1615 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615
  have eq1814 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X0 X0) X1))) = (k X0 (M.op X1 (M.op (M.op X0 X0) X1))) ∨ (k X0 (M.op X1 (M.op (M.op X0 X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq329 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq1818 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op (M.op X0 X0) X1))) = X0 ∨ (k X0 (M.op X1 (M.op (M.op X0 X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1814 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq1814
    | (have j0 := eq1814 X0 X1
       grind)
    | exact resolve eq1814 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq1819 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op (M.op X0 X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1818 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818
  have eq1846 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op (M.op (σ X0) (σ X0)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (M.op X1 (M.op (M.op (σ X0) (σ X0)) X1))
       have i₂ := eq1819 (σ X0) X1
       grind)
    | exact superpose eq1819 eq29
    | exact resolve eq29 eq1819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1819
  have eq1877 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op (σ (M.op X0 X0)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1846 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq1846
    | exact resolve eq1846 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846
  have eq1886 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (M.op (σ (M.op X0 X0)) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1877 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1877
    | exact resolve eq1877 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq2063 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (τ (M.op X1 (M.op (σ (σ (M.op X0 X0))) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1886 (σ X0) X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq1886
    | exact resolve eq1886 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2097 : ∀ X0 X1 X2 : G, (τ (k (σ X0) X2)) = (k (k X0 (τ (τ (M.op X1 (M.op (σ (M.op (σ X0) (σ X0))) X1))))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X0 (τ (M.op X1 (M.op (σ (M.op (σ X0) (σ X0))) X1))) X2
       have i₂ := eq1886 (σ X0) X1
       grind)
    | exact superpose eq1886 eq60
    | exact resolve eq60 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1886
  have eq2126 : ∀ X0 X1 X2 : G, (τ (k (σ X0) X2)) = (k (k X0 (τ (τ (M.op X1 (M.op (σ (σ (M.op X0 X0))) X1))))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2097 X0 X1 X2
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq2097
    | exact resolve eq2097 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2097
  have eq2147 : ∀ X0 X1 X2 : G, (k X0 (τ X2)) = (k (k X0 (τ (τ (M.op X1 (M.op (σ (σ (M.op X0 X0))) X1))))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2126 X0 X1 X2
       have i₂ := eq29 X0 X2
       grind)
    | exact superpose eq29 eq2126
    | exact resolve eq2126 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2126
  have eq52371 : ∀ X0 X1 X2 : G, (σ (k X0 (τ X1))) = (k (σ X0) (τ (M.op X2 (M.op (σ (σ (M.op X0 X0))) X2)))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (k (σ X0) (τ (M.op X2 (M.op (σ (σ (M.op X0 X0))) X2))))) ∨ (σ (k X0 (τ X1))) = (M.op (k (σ X0) (τ (M.op X2 (M.op (σ (σ (M.op X0 X0))) X2)))) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1420 X0 (τ (M.op X1 (M.op (σ (σ (M.op X0 X0))) X1))) (τ X2)
       have i₂ := eq2147 X0 X1 X2
       grind)
    | exact superpose eq2147 eq1420
    | (have j0 := eq1420 X0 (τ (M.op X2 (M.op (σ (σ (M.op X0 X0))) X2))) (τ X1)
       grind)
    | exact resolve eq1420 eq2147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420 eq2147
  have eq52673 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k X0 (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (k (σ X0) (τ (M.op X2 (M.op (σ (σ (M.op X0 X0))) X2))))) ∨ (σ (k X0 (τ X1))) = (M.op (k (σ X0) (τ (M.op X2 (M.op (σ (σ (M.op X0 X0))) X2)))) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52371 X0 X1 X2
       have i₂ := eq2063 X0 X2
       grind)
    | exact superpose eq2063 eq52371
    | (have j0 := eq52371 X0 X1 X2
       grind)
    | exact resolve eq52371 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52371
  have eq52739 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (k (σ X0) (τ (M.op X2 (M.op (σ (σ (M.op X0 X0))) X2))))) ∨ (σ (k X0 (τ X1))) = (M.op (k (σ X0) (τ (M.op X2 (M.op (σ (σ (M.op X0 X0))) X2)))) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52673 X0 X1 X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq52673
    | (have j0 := eq52673 X0 X1 X2
       grind)
    | exact resolve eq52673 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52673
  have eq52802 : ∀ X0 X1 X2 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ X0)) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ (k X0 (τ X1))) = (M.op (k (σ X0) (τ (M.op X2 (M.op (σ (σ (M.op X0 X0))) X2)))) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52739 X0 X1 X2
       have i₂ := eq2063 X0 X2
       grind)
    | exact superpose eq2063 eq52739
    | (have j0 := eq52739 X0 X1 X2
       grind)
    | exact resolve eq52739 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52739
  have eq52861 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ (k X0 (τ X1))) = (M.op (k (σ X0) (τ (M.op X2 (M.op (σ (σ (M.op X0 X0))) X2)))) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52802 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq52802
    | (have j0 := eq52802 X0 X1 X2
       grind)
    | exact resolve eq52802 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52802
  have eq52899 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ (k X0 (τ X1))) = (M.op (k (σ X0) (τ (M.op X2 (M.op (σ (σ (M.op X0 X0))) X2)))) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52861 X0 X1 X2
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq52861
    | (have j0 := eq52861 X0 X1 X2
       grind)
    | exact resolve eq52861 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq52861
  have eq52924 : ∀ X0 X1 X2 : G, (σ (k X0 (τ X1))) = (M.op (k (σ X0) (τ (M.op X2 (M.op (σ (σ (M.op X0 X0))) X2)))) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52899 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq52899
    | (have j0 := eq52899 X0 X1 X2
       grind)
    | exact resolve eq52899 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52899
  have eq52946 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52924 X0 X1 x
       have i₂ := eq2063 X0 x
       grind)
    | exact superpose eq2063 eq52924
    | (have j0 := eq52924 X0 X1 x
       grind)
    | exact resolve eq52924 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2063 eq52924
  have eq52964 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52946 X0 X1
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq52946
    | (have j0 := eq52946 X0 X1
       grind)
    | exact resolve eq52946 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq52946
  have eq52979 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq52964 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq52964 X0 (σ X0)
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq52964 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq52964 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52964
  have eq52997 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52979 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52979
    | exact resolve eq52979 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52979
  have eq53570 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1533
       have i₂ := eq52997 x y
       grind)
    | exact superpose eq52997 eq1533
    | (have j1 := eq52997 x y
       grind)
    | exact resolve eq1533 eq52997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq53572 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq52997 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52997
  have eq53574 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq53570
  have eq54100 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq53572 (σ x) (σ y)
       have i₂ := eq53574
       grind)
    | exact superpose eq53574 eq53572
    | (have j0 := eq53572 (σ x) (σ y)
       grind)
    | (have r₁ := eq53572 (σ x) (σ y)
       have r₂ := eq53574
       grind)
    | exact resolve eq53572 eq53574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53574
  have eq54101 : (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq54100
  have eq54103 : x = (k x y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq54101
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq54101
    | exact resolve eq54101 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54101
  have eq54827 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq1556 x y
       have i₂ := eq54103
       grind)
    | exact superpose eq54103 eq1556
    | (have j0 := eq1556 x y
       grind)
    | (have r₁ := eq1556 x y
       have r₂ := eq54103
       grind)
    | exact resolve eq1556 eq54103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54103
  have eq54856 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq54827
  have eq54864 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1556 x y
       grind)
    | (have r₁ := eq54856
       have r₂ := eq1556 x y
       grind)
    | exact resolve eq54856 eq1556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556 eq54856
  have eq55414 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq54864
       grind)
    | exact superpose eq54864 eq16
    | exact resolve eq16 eq54864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55418 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq53572 (σ x) (σ y)
       have i₂ := eq54864
       grind)
    | exact superpose eq54864 eq53572
    | (have j0 := eq53572 (σ x) (σ y)
       grind)
    | (have r₁ := eq53572 (σ x) (σ y)
       have r₂ := eq54864
       grind)
    | exact resolve eq53572 eq54864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53572 eq54864
  have eq55419 : (σ x) = (k (σ x) (σ y)) := by grind
  clear eq55418
  have eq55421 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq55419
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq55419
    | exact resolve eq55419 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55419
  have eq56208 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq55421
       grind)
    | exact superpose eq55421 eq10
    | exact resolve eq10 eq55421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55421
  have eq56341 : x = (k x y) := by
    first
    | (have i₁ := eq56208
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq56208
    | exact resolve eq56208 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56208
  have eq56368 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1616 x y
       have i₂ := eq56341
       grind)
    | exact superpose eq56341 eq1616
    | (have j0 := eq1616 x y
       grind)
    | (have r₁ := eq1616 x y
       have r₂ := eq56341
       grind)
    | exact resolve eq1616 eq56341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616 eq56341
  have eq56393 : x = (M.op x y) := by grind
  clear eq56368
  have eq56791 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq55414
       have i₂ := eq56393
       grind)
    | exact superpose eq56393 eq55414
    | exact resolve eq55414 eq56393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55414 eq56393
  have eq56801 : False := by grind
  exact eq56801

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq205 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq815 : ∀ X0 X1 : G, (σ (σ (k X0 X1))) ≠ (σ (σ X1)) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq205 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq205
    | (have j0 := eq205 (σ X0) (σ X1)
       grind)
    | exact resolve eq205 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq3254 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq86 X1 X0
       grind)
    | exact superpose eq86 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq86 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq86 X0 (σ X0)
       grind)
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3271 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq86 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq3272 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3271 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3271
  have eq3273 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3254 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3254
  have eq3274 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3273 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3273
  have eq3276 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3272 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3272
    | (have j0 := eq3272 X0
       grind)
    | exact resolve eq3272 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3272
  have eq3335 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq3276 X0
       grind)
    | exact superpose eq3276 eq38
    | (have j1 := eq3276 X0
       grind)
    | exact resolve eq38 eq3276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq3276
  have eq3349 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3335 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3335
    | (have j0 := eq3335 X0
       grind)
    | exact resolve eq3335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3335
  have eq3350 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3349 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349
  have eq3352 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3350 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3350
    | exact resolve eq3350 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3374 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq3350 X0
       grind)
    | exact superpose eq3350 eq11
    | exact resolve eq11 eq3350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3350
  have eq3427 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3352 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq3352
    | exact resolve eq3352 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352
  have eq3622 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3427 X0
       grind)
    | exact superpose eq3427 eq11
    | exact resolve eq11 eq3427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3719 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3622 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3622
    | exact resolve eq3622 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3622
  have eq3779 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq3719 (τ X0)
       grind)
    | exact superpose eq3719 eq34
    | exact resolve eq34 eq3719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3828 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3779 X0
       have i₂ := eq3427 X0
       grind)
    | exact superpose eq3427 eq3779
    | exact resolve eq3779 eq3427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3427 eq3779
  have eq4306 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq4322 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4306 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq4306
    | exact resolve eq4306 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4306
  have eq4357 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4322 X0
       have i₂ := eq3719 X0
       grind)
    | exact superpose eq3719 eq4322
    | exact resolve eq4322 eq3719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4322
  have eq4376 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq4357
  have eq24683 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1) X0
       have i₂ := eq3274 (σ X0) X1
       grind)
    | exact superpose eq3274 eq24
    | (have j1 := eq3274 (σ X0) X1
       grind)
    | exact resolve eq24 eq3274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3274
  have eq24765 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24683 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq24683
    | (have j0 := eq24683 X0 X1
       grind)
    | exact resolve eq24683 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24683
  have eq24844 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24765 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24765
    | (have j0 := eq24765 X0 X1
       grind)
    | exact resolve eq24765 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24765
  have eq24914 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24844 X0 X1
       have i₂ := eq3374 X0
       grind)
    | exact superpose eq3374 eq24844
    | (have j0 := eq24844 X0 X1
       grind)
    | exact resolve eq24844 eq3374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24844
  have eq24962 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24914 X0 X1
       have i₂ := eq3719 X0
       grind)
    | exact superpose eq3719 eq24914
    | (have j0 := eq24914 X0 X1
       grind)
    | exact resolve eq24914 eq3719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24914
  have eq25001 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24962 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24962
    | (have j0 := eq24962 X0 X1
       grind)
    | exact resolve eq24962 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24962
  have eq25579 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq815 (τ X0) (τ X1)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq815
    | (have j0 := eq815 (τ X0) (τ X1)
       grind)
    | exact resolve eq815 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq25654 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25579 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq25579
    | (have j0 := eq25579 X0 X1
       grind)
    | exact resolve eq25579 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25579
  have eq25708 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25654 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq25654
    | (have j0 := eq25654 X0 X1
       grind)
    | exact resolve eq25654 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25654
  have eq25760 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25708 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25708
    | (have j0 := eq25708 X0 X1
       grind)
    | exact resolve eq25708 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25708
  have eq25809 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25760 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25760
    | (have j0 := eq25760 X0 X1
       grind)
    | exact resolve eq25760 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25760
  have eq25850 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25809 X0 X1
       have i₂ := eq3374 (σ (τ X1))
       grind)
    | exact superpose eq3374 eq25809
    | (have j0 := eq25809 X0 X1
       grind)
    | exact resolve eq25809 eq3374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3374 eq25809
  have eq25889 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25850 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq25850
    | (have j0 := eq25850 X0 X1
       grind)
    | exact resolve eq25850 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25850
  have eq25926 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25889 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq25889
    | (have j0 := eq25889 X0 X1
       grind)
    | exact resolve eq25889 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq25889
  have eq25956 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (σ (τ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25926 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq25926
    | (have j0 := eq25926 X0 X1
       grind)
    | exact resolve eq25926 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25926
  have eq25982 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25956 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25956
    | (have j0 := eq25956 X0 X1
       grind)
    | exact resolve eq25956 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25956
  have eq26007 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25982 X0 X1
       have i₂ := eq3719 X1
       grind)
    | exact superpose eq3719 eq25982
    | (have j0 := eq25982 X0 X1
       grind)
    | exact resolve eq25982 eq3719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3719 eq25982
  have eq29977 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (σ (M.op X1 X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq25001 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25001
    | (have j0 := eq25001 X1 (τ X0)
       grind)
    | exact resolve eq25001 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30057 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq25001 X1 X0
       grind)
    | exact superpose eq25001 eq11
    | (have j1 := eq25001 X1 X0
       grind)
    | exact resolve eq11 eq25001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25001
  have eq30490 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (M.op (τ X1) (τ X1))) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq29977 X1 (τ X0)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq29977
    | (have j0 := eq29977 X0 (τ X1)
       grind)
    | exact resolve eq29977 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq29977
  have eq30692 : ∀ X0 X1 : G, (σ (τ (M.op X1 X1))) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30490 X0 X1
       have i₂ := eq3828 X1
       grind)
    | exact superpose eq3828 eq30490
    | (have j0 := eq30490 X0 X1
       grind)
    | exact resolve eq30490 eq3828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3828 eq30490
  have eq30781 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30692 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq30692
    | (have j0 := eq30692 X0 X1
       grind)
    | exact resolve eq30692 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30692
  have eq30856 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30781 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq30781
    | (have j0 := eq30781 X0 X1
       grind)
    | exact resolve eq30781 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30781
  have eq31864 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq30856 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30856
  have eq34480 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30057 x y
       grind)
    | exact superpose eq30057 eq16
    | (have j1 := eq30057 x y
       grind)
    | exact resolve eq16 eq30057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30057
  have eq34957 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq34480
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq34480
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq34480 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34480
  have eq34960 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq34957
  have eq34961 : y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq34960
  have eq35564 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31864 x y
       have i₂ := eq34961
       grind)
    | exact superpose eq34961 eq31864
    | (have j0 := eq31864 x y
       grind)
    | exact resolve eq31864 eq34961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31864
  have eq35568 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq35564
  have eq35569 : x = (M.op y y) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq35568
  have eq36212 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4376 y
       have i₂ := eq35569
       grind)
    | exact superpose eq35569 eq4376
    | exact resolve eq4376 eq35569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35569
  have eq36232 : (σ x) = (σ (M.op y y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq36212
       have r₂ := eq16
       grind)
    | exact resolve eq36212 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36212
  have eq36253 : (M.op y y) = (τ (σ x)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq36232
       grind)
    | exact superpose eq36232 eq10
    | exact resolve eq10 eq36232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36232
  have eq36383 : x = (M.op y y) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq36253
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq36253
    | exact resolve eq36253 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36253
  have eq36944 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq4376 y
       have i₂ := eq36383
       grind)
    | exact superpose eq36383 eq4376
    | exact resolve eq4376 eq36383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36383
  have eq36964 : (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq36944
       have r₂ := eq16
       grind)
    | exact resolve eq36944 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36944
  have eq36979 : (k x y) = (σ (τ y)) := by
    first
    | (have i₁ := eq11 (k x y)
       have i₂ := eq36964
       grind)
    | exact superpose eq36964 eq11
    | exact resolve eq11 eq36964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36964
  have eq37162 : y = (k x y) := by
    first
    | (have i₁ := eq36979
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq36979
    | exact resolve eq36979 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36979
  have eq37715 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq26007 x y
       have i₂ := eq37162
       grind)
    | exact superpose eq37162 eq26007
    | (have j0 := eq26007 x y
       grind)
    | exact resolve eq26007 eq37162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26007 eq37162
  have eq37716 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq37715
  have eq40995 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37716
       grind)
    | exact superpose eq37716 eq16
    | exact resolve eq16 eq37716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37716
  have eq41015 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40995
       have i₂ := eq34961
       grind)
    | exact superpose eq34961 eq40995
    | exact resolve eq40995 eq34961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34961 eq40995
  have eq41016 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq41015
  have eq41017 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq41016
  have eq41526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4376 y
       have i₂ := eq41017
       grind)
    | exact superpose eq41017 eq4376
    | exact resolve eq4376 eq41017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41017
  have eq41546 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq41526
       have r₂ := eq16
       grind)
    | exact resolve eq41526 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41526
  have eq41567 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq41546
       grind)
    | exact superpose eq41546 eq10
    | exact resolve eq10 eq41546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41546
  have eq41699 : x = (M.op y y) := by
    first
    | (have i₁ := eq41567
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq41567
    | exact resolve eq41567 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41567
  have eq42255 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4376 y
       have i₂ := eq41699
       grind)
    | exact superpose eq41699 eq4376
    | exact resolve eq4376 eq41699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4376 eq41699
  have eq42275 : False := by grind
  exact eq42275

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq20 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq20 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq20 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq36 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq32 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq36 X1 X0
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq36 X0 X1
       grind)
    | exact resolve eq40 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq40
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq21 X1
       grind)
    | exact superpose eq21 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq45
  have eq95 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq99 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       have j1 := eq48 X0 X1
       grind)
    | (have r₁ := eq95 X0 X1
       have r₂ := eq48 X0 X1
       grind)
    | (have r₁ := eq95 X1 X1
       have r₂ := eq48 X1 X1
       grind)
    | exact resolve eq95 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq95
  have eq220 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq99 (σ X0) (σ X1)
       grind)
    | exact superpose eq99 eq15
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq220 X0 X1
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq220
    | exact resolve eq220 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq220
  have eq230 : False := by grind
  exact eq230

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq266 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq269 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq267 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq267 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq280 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq269 (σ X0)
       grind)
    | exact superpose eq269 eq15
    | exact resolve eq15 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq280
    | exact resolve eq280 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq280
  have eq342 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq346 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq342 X0 X1
       have j1 := eq343 X0 X1
       grind)
    | (have r₁ := eq342 X0 X1
       have r₂ := eq343 X0 X1
       grind)
    | exact resolve eq342 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq343
  have eq411 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq346 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq346
    | exact resolve eq346 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq346 y (σ x)
       grind)
    | exact superpose eq346 eq16
    | (have j1 := eq346 y (σ x)
       grind)
    | exact resolve eq16 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq431 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq422
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq422
    | exact resolve eq422 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq446 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq411 X0 X1
       grind)
    | exact superpose eq411 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq411 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq411 X0 X1
       grind)
    | exact resolve eq13 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq446 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq466 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq459 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq459 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq459 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq491 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq466 X1 (τ X0)
       grind)
    | exact superpose eq466 eq17
    | (have j1 := eq466 X1 (τ X0)
       grind)
    | exact resolve eq17 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq497 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq466 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq491 X1 (τ X0)
       grind)
    | exact superpose eq491 eq18
    | (have j1 := eq491 X1 (τ X0)
       grind)
    | exact resolve eq18 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq491
  have eq709 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq702 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq702
    | (have j0 := eq702 X0 X1
       grind)
    | exact resolve eq702 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq724 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq709 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq709
    | (have j0 := eq709 X0 X1
       grind)
    | exact resolve eq709 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq727 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq724 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq724
    | (have j0 := eq724 X0 X1
       grind)
    | exact resolve eq724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq784 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq727 X0 X1
       have i₂ := eq466 X0 X1
       grind)
    | exact superpose eq466 eq727
    | (have j0 := eq727 X1 X0
       have j1 := eq466 X1 X0
       grind)
    | exact resolve eq727 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466 eq727
  have eq847 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq784 X0 X1
       have j1 := eq497 X0 X1
       grind)
    | (have r₁ := eq784 X0 X1
       have r₂ := eq497 X0 X1
       grind)
    | exact resolve eq784 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497 eq784
  have eq888 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq847 X1 (σ X0)
       grind)
    | exact superpose eq847 eq22
    | (have j1 := eq847 X1 (σ X0)
       grind)
    | exact resolve eq22 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq847
  have eq924 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq888 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq888
    | (have j0 := eq888 X0 X1
       grind)
    | exact resolve eq888 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq943 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq924 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq924
    | (have j0 := eq924 X0 X1
       grind)
    | exact resolve eq924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq1183 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq943 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq943
    | exact resolve eq943 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq1251 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1183 x y
       grind)
    | exact superpose eq1183 eq16
    | (have j1 := eq1183 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1183 x y
       grind)
    | exact resolve eq16 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1267 : y = (k x y) := by grind
  clear eq1251
  have eq1434 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq431
       have i₂ := eq411 y x
       grind)
    | exact superpose eq411 eq431
    | (have j1 := eq411 y x
       grind)
    | exact resolve eq431 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1435 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq1434
  have eq1436 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1435
       have i₂ := eq1267
       grind)
    | exact superpose eq1267 eq1435
    | exact resolve eq1435 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435
  have eq1437 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1436
       have i₂ := eq1267
       grind)
    | exact superpose eq1267 eq1436
    | exact resolve eq1436 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436
  have eq1438 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq431
       have i₂ := eq1437
       grind)
    | exact superpose eq1437 eq431
    | exact resolve eq431 eq1437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq1437
  have eq1445 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1438
  have eq1446 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1445
       have i₂ := eq1267
       grind)
    | exact superpose eq1267 eq1445
    | exact resolve eq1445 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445
  have eq1447 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1446
  have eq1449 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1447
       grind)
    | exact superpose eq1447 eq16
    | exact resolve eq16 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447
  have eq1464 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1449
       have i₂ := eq411 y x
       grind)
    | exact superpose eq411 eq1449
    | (have j1 := eq411 y x
       grind)
    | exact resolve eq1449 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq1465 : (M.op x y) = (k x y) := by grind
  clear eq1464
  have eq1467 : y = (M.op x y) := by
    first
    | (have i₁ := eq1465
       have i₂ := eq1267
       grind)
    | exact superpose eq1267 eq1465
    | exact resolve eq1465 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267 eq1465
  have eq1468 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1449
       have i₂ := eq1467
       grind)
    | exact superpose eq1467 eq1449
    | exact resolve eq1449 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449 eq1467
  have eq1477 : False := by grind
  exact eq1477

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq271 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq271 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq274 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq272 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq272 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq272 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq285 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq274 (σ X0)
       grind)
    | exact superpose eq274 eq15
    | exact resolve eq15 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq274 (τ X0)
       grind)
    | exact superpose eq274 eq31
    | exact resolve eq31 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq291 X0
       have i₂ := eq274 X0
       grind)
    | exact superpose eq274 eq291
    | exact resolve eq291 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq304 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq285 X0
       have i₂ := eq274 X0
       grind)
    | exact superpose eq274 eq285
    | exact resolve eq285 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq285
  have eq348 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq304 X0
       grind)
    | exact superpose eq304 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq304 X0
       grind)
    | exact superpose eq304 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq353 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq348 X0 X1
       have j1 := eq350 X0 X1
       grind)
    | (have r₁ := eq348 X0 X1
       have r₂ := eq350 X0 X1
       grind)
    | exact resolve eq348 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq350
  have eq366 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq371 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq366 X0 X1
       have j1 := eq368 X0 X1
       grind)
    | (have r₁ := eq366 X0 X1
       have r₂ := eq368 X0 X1
       grind)
    | exact resolve eq366 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq368
  have eq436 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq353 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq353
    | exact resolve eq353 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq475 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq436 X0 X1
       grind)
    | exact superpose eq436 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq436 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq436 X0 X1
       grind)
    | exact resolve eq13 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq436 (σ x) (σ y)
       grind)
    | exact superpose eq436 eq16
    | (have j1 := eq436 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq482 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq475 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq485 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq477
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq477
    | exact resolve eq477 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq486 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq482 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq482 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq482 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq489 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq486 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq486
    | exact resolve eq486 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq486 X0 (τ X1)
       grind)
    | exact superpose eq486 eq17
    | (have j1 := eq486 X0 (τ X1)
       grind)
    | exact resolve eq17 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq517 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq486 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1089 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq371 X0 X1
       grind)
    | exact superpose eq371 eq18
    | (have j1 := eq371 X0 X1
       grind)
    | exact resolve eq18 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1327 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq511 (τ X0) X1
       grind)
    | exact superpose eq511 eq18
    | (have j1 := eq511 (τ X0) X1
       grind)
    | exact resolve eq18 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq511
  have eq1336 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1327 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1327
    | (have j0 := eq1327 X0 X1
       grind)
    | exact resolve eq1327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327
  have eq1351 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1336 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1336
    | (have j0 := eq1336 X0 X1
       grind)
    | exact resolve eq1336 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq1354 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1351 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1351
    | (have j0 := eq1351 X0 X1
       grind)
    | exact resolve eq1351 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351
  have eq1420 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1354 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1354
    | (have j0 := eq1354 X1 (σ X0)
       grind)
    | exact resolve eq1354 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq2102 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1420 X0 X0
       have i₂ := eq486 X0 (σ X0)
       grind)
    | exact superpose eq486 eq1420
    | (have j0 := eq1420 X1 X0
       have j1 := eq486 X0 (σ X1)
       grind)
    | exact resolve eq1420 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486 eq1420
  have eq2142 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2102 X0 X1
       have j1 := eq517 (σ X1) X0
       grind)
    | (have r₁ := eq2102 X1 X1
       have r₂ := eq517 (σ X1) X1
       grind)
    | exact resolve eq2102 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq2102
  have eq2454 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq2142 (σ X0) X1
       grind)
    | exact superpose eq2142 eq22
    | (have j1 := eq2142 (σ X0) X1
       grind)
    | exact resolve eq22 eq2142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142
  have eq2467 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2454 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2454
    | (have j0 := eq2454 X0 X1
       grind)
    | exact resolve eq2454 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454
  have eq2485 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2467 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2467
    | (have j0 := eq2467 X0 X1
       grind)
    | exact resolve eq2467 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2467
  have eq2494 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2485 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2485
    | (have j0 := eq2485 X0 X1
       grind)
    | exact resolve eq2485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2485
  have eq2665 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2494 x y
       grind)
    | exact superpose eq2494 eq16
    | (have j1 := eq2494 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2494 x y
       grind)
    | exact resolve eq16 eq2494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2494
  have eq2703 : x = (k y x) := by grind
  clear eq2665
  have eq4286 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq489 X1 X0
       grind)
    | exact superpose eq489 eq10
    | (have j1 := eq489 X1 X0
       grind)
    | exact resolve eq10 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq4340 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4286 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4286
    | (have j0 := eq4286 X0 X1
       grind)
    | exact resolve eq4286 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4286
  have eq4369 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4340 (τ X0) (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq4340
    | exact resolve eq4340 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4340
  have eq4430 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4369 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4369
    | (have j0 := eq4369 X0 X1
       grind)
    | exact resolve eq4369 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4369
  have eq4440 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4430 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4430
    | (have j0 := eq4430 X0 X1
       grind)
    | exact resolve eq4430 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4430
  have eq4443 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4440 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4440
    | (have j0 := eq4440 X0 X1
       grind)
    | exact resolve eq4440 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4440
  have eq4459 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq4443 X1 (σ X0)
       grind)
    | exact superpose eq4443 eq22
    | (have j1 := eq4443 X1 (σ X0)
       grind)
    | exact resolve eq22 eq4443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4443
  have eq4505 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4459 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4459
    | (have j0 := eq4459 X0 X1
       grind)
    | exact resolve eq4459 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4459
  have eq4556 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq371 X0 (τ X1)
       have i₂ := eq4505 (τ X0) X1
       grind)
    | exact superpose eq4505 eq371
    | (have j0 := eq371 X0 (τ X1)
       have j1 := eq4505 (τ X0) X1
       grind)
    | exact resolve eq371 eq4505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq4505
  have eq4560 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X1)) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq4556 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4556
  have eq4567 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4560 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4560
    | (have j0 := eq4560 X0 X1
       grind)
    | exact resolve eq4560 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4560
  have eq4626 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4567 (σ X0) (σ X1)
       grind)
    | exact superpose eq4567 eq15
    | (have j1 := eq4567 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq4567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4567
  have eq4666 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4626 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4626
    | (have j0 := eq4626 X0 X1
       grind)
    | exact resolve eq4626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4626
  have eq4684 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4666 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4666
    | (have j0 := eq4666 X0 X1
       grind)
    | exact resolve eq4666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4666
  have eq4737 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4684 x y
       grind)
    | exact superpose eq4684 eq16
    | (have j1 := eq4684 x y
       grind)
    | exact resolve eq16 eq4684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4684
  have eq4831 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4737
       have i₂ := eq2703
       grind)
    | exact superpose eq2703 eq4737
    | exact resolve eq4737 eq2703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4737
  have eq6325 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1089 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1089
    | exact resolve eq1089 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq6448 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6325 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq6325
    | (have j0 := eq6325 X0 X1
       grind)
    | exact resolve eq6325 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6325
  have eq6494 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6448 x y
       have i₂ := eq2703
       grind)
    | exact superpose eq2703 eq6448
    | (have j0 := eq6448 x y
       grind)
    | exact resolve eq6448 eq2703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6448
  have eq6572 : x = (M.op x y) := by
    first
    | (have r₁ := eq6494
       have r₂ := eq4831
       grind)
    | exact resolve eq6494 eq4831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4831 eq6494
  have eq6574 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq485
       have i₂ := eq6572
       grind)
    | exact superpose eq6572 eq485
    | exact resolve eq485 eq6572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq6586 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq6574
  have eq6587 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6586
       have i₂ := eq2703
       grind)
    | exact superpose eq2703 eq6586
    | exact resolve eq6586 eq2703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703 eq6586
  have eq6590 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6587
       grind)
    | exact superpose eq6587 eq16
    | exact resolve eq16 eq6587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6587
  have eq6615 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq6590
       have i₂ := eq6572
       grind)
    | exact superpose eq6572 eq6590
    | exact resolve eq6590 eq6572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6572 eq6590
  have eq6616 : False := by grind
  exact eq6616
