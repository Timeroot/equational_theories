import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pyx_pyx_pxx_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
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
       have r₂ := eq12 x x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
       have j1 := eq14 X1 X0
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
  have eq29 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
       have j1 := eq14 X1 X0
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq29 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq29 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq36 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq36 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq42
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq46 X0 X1
       grind)
    | (have r₁ := eq47 X0 X1
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq47 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq47
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq95 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       have j1 := eq49 X1 X0
       grind)
    | (have r₁ := eq91 X1 X1
       have r₂ := eq49 X1 X1
       grind)
    | (have r₁ := eq91 X1 X0
       have r₂ := eq49 X0 X1
       grind)
    | exact resolve eq91 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq91
  have eq196 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq95 (σ X1) (σ X0)
       grind)
    | exact superpose eq95 eq15
    | exact resolve eq15 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq196 X0 X1
       have i₂ := eq95 X1 X0
       grind)
    | exact superpose eq95 eq196
    | exact resolve eq196 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq196
  have eq205 : False := by grind
  exact eq205

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyx_pyx_pxy_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  clear eq17
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
  have eq444 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op (σ X0) X1) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq22
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq22 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3173 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq444 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq444
    | exact resolve eq444 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq3250 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3173 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq3173
    | (have j0 := eq3173 X0 X1
       grind)
    | exact resolve eq3173 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3173
  have eq3272 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq3250 X1 X0
       grind)
    | exact superpose eq3250 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq3250 X1 X0
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq3250 X0 X1
       grind)
    | exact resolve eq12 eq3250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3250
  have eq3313 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3272 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3272
  have eq3424 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq3313 X1 X0
       grind)
    | exact superpose eq3313 eq11
    | (have j1 := eq3313 X1 X0
       grind)
    | exact resolve eq11 eq3313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3313
  have eq3542 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3424 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3424
    | (have j0 := eq3424 X0 X1
       grind)
    | exact resolve eq3424 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3424
  have eq3543 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3542 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3542
  have eq3640 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq3543 (σ X0) X1
       grind)
    | exact superpose eq3543 eq22
    | (have j1 := eq3543 (σ X0) X1
       grind)
    | exact resolve eq22 eq3543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq3721 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3640 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3640
    | exact resolve eq3640 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3640
  have eq3809 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3721 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq3721
    | (have j0 := eq3721 X0 X1
       grind)
    | exact resolve eq3721 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3721
  have eq3812 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X1) (σ X0))) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3809 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3809
    | (have j0 := eq3809 (σ X1) (σ X0)
       grind)
    | exact resolve eq3809 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3809
  have eq3961 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3812 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3812
    | (have j0 := eq3812 X0 X1
       grind)
    | exact resolve eq3812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3812
  have eq7435 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq3961 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq3961 X0 X1
       grind)
    | exact superpose eq3961 eq13
    | (have j1 := eq3961 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq3961 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq3961 X0 X1
       grind)
    | exact resolve eq13 eq3961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7436 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq3961 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq3961 X0 X1
       grind)
    | exact superpose eq3961 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq3961 X1 X0
       grind)
    | exact resolve eq12 eq3961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3961
  have eq7437 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq7435 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7435
  have eq7441 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7436 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7436
    | (have j0 := eq7436 X0 X1
       grind)
    | exact resolve eq7436 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7436
  have eq7442 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7437 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7437
    | (have j0 := eq7437 X0 X1
       grind)
    | exact resolve eq7437 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7437
  have eq7449 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq7442 X0 X1
       have j1 := eq7441 X0 X1
       grind)
    | (have r₁ := eq7442 X0 X1
       have r₂ := eq7441 X0 X1
       grind)
    | exact resolve eq7442 eq7441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7441 eq7442
  have eq7511 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7449 x y
       grind)
    | exact superpose eq7449 eq16
    | (have j1 := eq7449 x y
       grind)
    | exact resolve eq16 eq7449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7449
  have eq7591 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq7511
       have i₂ := eq3543 x y
       grind)
    | exact superpose eq3543 eq7511
    | (have j1 := eq3543 x y
       grind)
    | exact resolve eq7511 eq3543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3543
  have eq7598 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq7591
  have eq7608 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq7598
       grind)
    | exact superpose eq7598 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq7598
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq7598
       grind)
    | exact resolve eq13 eq7598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7609 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq7598
       grind)
    | exact superpose eq7598 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq7598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7598
  have eq7610 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq7608
  have eq7612 : (M.op x y) = (k y x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq7610
       have r₂ := eq7609
       grind)
    | exact resolve eq7610 eq7609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7609 eq7610
  have eq7624 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq7511
       have i₂ := eq7612
       grind)
    | exact superpose eq7612 eq7511
    | exact resolve eq7511 eq7612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7511 eq7612
  have eq7634 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq7624
  have eq7635 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq7634
  have eq7646 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq7635
       grind)
    | exact superpose eq7635 eq11
    | exact resolve eq11 eq7635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7635
  have eq7717 : False := by grind
  exact eq7717

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_y_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X1) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq31 (σ X0)
       grind)
    | exact superpose eq31 eq15
    | exact resolve eq15 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq33
    | exact resolve eq33 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq33
  have eq42 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq54 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op (M.op (M.op X0 X0) X1) X1) X0) = X0 ∨ (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op (M.op (M.op X0 X0) X1) X1) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op (M.op (M.op X0 X0) X1) X1) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op (M.op X0 X0) X1) X1) X0
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X1)) ∨ (k (M.op (M.op (M.op X0 X0) X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq73 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq38
    | exact resolve eq38 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq38 X1
       grind)
    | exact superpose eq38 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq124 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op (M.op (M.op X0 X0) X1) X1) X0) = (k (M.op (M.op (M.op X0 X0) X1) X1) X0) ∨ (k (M.op (M.op (M.op X0 X0) X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (M.op (M.op X0 X0) X1) X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq12 (M.op (M.op (M.op X0 X0) X1) X1) X0
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq12 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq126 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X1) X0) = (k (M.op (M.op (M.op X0 X0) X1) X1) X0) ∨ (k (M.op (M.op (M.op X0 X0) X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq124 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq127 : ∀ X0 X1 : G, (k (M.op (M.op (M.op X0 X0) X1) X1) X0) = X0 ∨ (k (M.op (M.op (M.op X0 X0) X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq126 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq126
    | (have j0 := eq126 X0 X1
       grind)
    | exact resolve eq126 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq128 : ∀ X0 X1 : G, (k (M.op (M.op (M.op X0 X0) X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq146 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (M.op (M.op (σ X0) (σ X0)) X1) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (M.op (M.op (σ X0) (σ X0)) X1) X1) X0
       have i₂ := eq128 (σ X0) X1
       grind)
    | exact superpose eq128 eq22
    | exact resolve eq22 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq151 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (M.op (σ (M.op X0 X0)) X1) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq146
    | exact resolve eq146 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq153 : ∀ X0 X1 : G, (k (τ (M.op (M.op (σ (M.op X0 X0)) X1) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq151
    | exact resolve eq151 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq154 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq87
    | exact resolve eq87 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq176 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq159 X0 X1 X2
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq159
    | (have j0 := eq159 X0 X1 X2
       grind)
    | exact resolve eq159 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq159
  have eq179 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq154 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq154
    | (have j0 := eq154 X0 X1
       grind)
    | exact resolve eq154 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq154
  have eq185 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq179 X0 X1
       have j1 := eq75 X1 X0
       grind)
    | (have r₁ := eq179 X1 X0
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq179 (σ X0) (M.op X0 X0)
       have r₂ := eq75 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq179 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq179
  have eq227 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op (M.op (σ (M.op (σ X0) (σ X0))) X1) X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (τ (M.op (M.op (σ (M.op (σ X0) (σ X0))) X1) X1)) X0
       have i₂ := eq153 (σ X0) X1
       grind)
    | exact superpose eq153 eq22
    | exact resolve eq22 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq232 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op (M.op (σ (σ (M.op X0 X0))) X1) X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq227 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq227
    | exact resolve eq227 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq238 : ∀ X0 X1 : G, (k (τ (τ (M.op (M.op (σ (σ (M.op X0 X0))) X1) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq232 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq232
    | exact resolve eq232 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq560 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq185 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq185
    | exact resolve eq185 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq1167 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (τ (M.op (M.op (σ (σ (M.op (σ X0) (σ X0)))) X1) X1)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (τ (τ (M.op (M.op (σ (σ (M.op (σ X0) (σ X0)))) X1) X1))) X0
       have i₂ := eq238 (σ X0) X1
       grind)
    | exact superpose eq238 eq22
    | exact resolve eq22 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq1181 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (τ (M.op (M.op (σ (σ (σ (M.op X0 X0)))) X1) X1)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1167 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq1167
    | exact resolve eq1167 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1194 : ∀ X0 X1 : G, (k (τ (τ (τ (M.op (M.op (σ (σ (σ (M.op X0 X0)))) X1) X1)))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1181 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1181
    | exact resolve eq1181 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181
  have eq2120 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k X0 (σ X1))
       have i₂ := eq176 X0 X1 X2
       grind)
    | exact superpose eq176 eq13
    | (have j0 := eq13 (σ X2) (k X0 (σ X1))
       have j1 := eq176 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq176 X0 X1 X2
       grind)
    | exact resolve eq13 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2122 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2120 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2120
  have eq2123 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2122 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122
  have eq2125 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k X2 (k (τ X0) X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2123 X0 X1 X2
       have i₂ := eq20 X0 X1 X2
       grind)
    | exact superpose eq20 eq2123
    | (have j0 := eq2123 X0 X1 X2
       grind)
    | exact resolve eq2123 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2123
  have eq4245 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (τ (τ (M.op (M.op (σ (σ (σ (M.op (σ X0) (σ X0))))) X1) X1))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (τ (τ (τ (M.op (M.op (σ (σ (σ (M.op (σ X0) (σ X0))))) X1) X1)))) X0
       have i₂ := eq1194 (σ X0) X1
       grind)
    | exact superpose eq1194 eq22
    | exact resolve eq22 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq4282 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (τ (τ (M.op (M.op (σ (σ (σ (σ (M.op X0 X0))))) X1) X1))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4245 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq4245
    | exact resolve eq4245 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4245
  have eq4311 : ∀ X0 X1 : G, (k (τ (τ (τ (τ (M.op (M.op (σ (σ (σ (σ (M.op X0 X0))))) X1) X1))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4282 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4282
    | exact resolve eq4282 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4282
  have eq13014 : ∀ X0 X1 : G, (σ X0) = (k (τ (τ (τ (τ (M.op (M.op (σ (σ (σ (σ (σ (M.op X0 X0)))))) X1) X1))))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4311 (σ X0) X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq4311
    | exact resolve eq4311 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13087 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (τ (τ (τ (M.op (M.op (σ (σ (σ (σ (M.op (σ X0) (σ X0)))))) X1) X1)))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (τ (τ (τ (τ (M.op (M.op (σ (σ (σ (σ (M.op (σ X0) (σ X0)))))) X1) X1))))) X0
       have i₂ := eq4311 (σ X0) X1
       grind)
    | exact superpose eq4311 eq22
    | exact resolve eq22 eq4311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4311
  have eq13164 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (τ (τ (τ (M.op (M.op (σ (σ (σ (σ (σ (M.op X0 X0)))))) X1) X1)))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13087 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq13087
    | exact resolve eq13087 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq13087
  have eq13215 : ∀ X0 X1 : G, (k (τ (τ (τ (τ (τ (M.op (M.op (σ (σ (σ (σ (σ (M.op X0 X0)))))) X1) X1)))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13164 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13164
    | exact resolve eq13164 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13164
  have eq47986 : ∀ X0 X1 X2 : G, (k X0 (σ (τ X1))) = (σ (k X2 (τ (k X0 X1)))) ∨ (M.op (k X0 (σ (τ X1))) (σ X2)) = (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) ∨ (M.op (σ X2) (k X0 (σ (τ X1)))) = (σ (k X2 (τ (k X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2125 X1 (τ X0) X2
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq2125
    | (have j0 := eq2125 X0 (τ X1) X2
       grind)
    | exact resolve eq2125 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq2125
  have eq48324 : ∀ X0 X1 X2 : G, (k X0 (σ (τ X1))) = (k (σ X2) (k X0 X1)) ∨ (M.op (k X0 (σ (τ X1))) (σ X2)) = (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) ∨ (M.op (σ X2) (k X0 (σ (τ X1)))) = (σ (k X2 (τ (k X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47986 X0 X1 X2
       have i₂ := eq18 (k X0 X1) X2
       grind)
    | exact superpose eq18 eq47986
    | (have j0 := eq47986 X0 X1 X2
       grind)
    | exact resolve eq47986 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47986
  have eq48378 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (σ X2) (k X0 X1)) ∨ (M.op (k X0 (σ (τ X1))) (σ X2)) = (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) ∨ (M.op (σ X2) (k X0 (σ (τ X1)))) = (σ (k X2 (τ (k X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48324 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq48324
    | (have j0 := eq48324 X0 X1 X2
       grind)
    | exact resolve eq48324 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48324
  have eq48431 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (σ X2)) = (M.op (k X0 X1) (k X0 X1)) ∨ (k X0 X1) = (k (σ X2) (k X0 X1)) ∨ (M.op (σ X2) (k X0 (σ (τ X1)))) = (σ (k X2 (τ (k X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48378 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48378
    | (have j0 := eq48378 X0 X1 X2
       grind)
    | exact resolve eq48378 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48378
  have eq48479 : ∀ X0 X1 X2 : G, (M.op (σ X2) (k X0 (σ (τ X1)))) = (k (σ X2) (k X0 X1)) ∨ (M.op (k X0 X1) (σ X2)) = (M.op (k X0 X1) (k X0 X1)) ∨ (k X0 X1) = (k (σ X2) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48431 X0 X1 X2
       have i₂ := eq18 (k X0 X1) X2
       grind)
    | exact superpose eq18 eq48431
    | (have j0 := eq48431 X0 X1 X2
       grind)
    | exact resolve eq48431 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq48431
  have eq48519 : ∀ X0 X1 X2 : G, (M.op (σ X2) (k X0 X1)) = (k (σ X2) (k X0 X1)) ∨ (M.op (k X0 X1) (σ X2)) = (M.op (k X0 X1) (k X0 X1)) ∨ (k X0 X1) = (k (σ X2) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48479 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq48479
    | (have j0 := eq48479 X0 X1 X2
       grind)
    | exact resolve eq48479 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48479
  have eq48544 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (σ X2) (k X0 X1)) ∨ (M.op (σ X2) (k X0 X1)) = (k (σ X2) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq48519 X0 X1 X2
       have j1 := eq12 (σ X2) (k X0 X1)
       grind)
    | (have r₁ := eq48519 X0 X1 X2
       have r₂ := eq12 (σ X2) (k X0 X1)
       grind)
    | exact resolve eq48519 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48519
  have eq113757 : ∀ X0 X1 X2 : G, (k X1 X2) ≠ (M.op (σ X0) (k X1 X2)) ∨ (k (σ X0) (k X1 X2)) = (M.op (σ X0) (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq48544 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48544
  have eq113773 : ∀ X0 X1 X2 : G, (k (σ X0) (k X1 X2)) = (M.op (σ X0) (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq113757 X0 X1 X2
       have j1 := eq560 (k X1 X2) (σ X0)
       grind)
    | (have r₁ := eq113757 X0 X1 X2
       have r₂ := eq560 (k X1 X2) (σ X0)
       grind)
    | exact resolve eq113757 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq113757
  have eq113976 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq113773 X0 (τ (τ (τ (τ (τ (M.op (M.op (σ (σ (σ (σ (σ (M.op X0 X0)))))) X1) X1)))))) X0
       have i₂ := eq13215 X0 X1
       grind)
    | exact superpose eq13215 eq113773
    | exact resolve eq113773 eq13215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13215
  have eq113989 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113773 X0 (τ (τ (τ (τ (M.op (M.op (σ (σ (σ (σ (σ (M.op X0 X0)))))) X1) X1))))) (σ X0)
       have i₂ := eq13014 X0 X1
       grind)
    | exact superpose eq13014 eq113773
    | exact resolve eq113773 eq13014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13014 eq113773
  have eq114237 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113989 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq113989
    | exact resolve eq113989 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113989
  have eq116663 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq113976 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq113976
    | exact resolve eq113976 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113976
  have eq128305 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq114237 y x
       grind)
    | exact superpose eq114237 eq16
    | exact resolve eq16 eq114237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114237
  have eq128725 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq128305
       have i₂ := eq116663 x y
       grind)
    | exact superpose eq116663 eq128305
    | exact resolve eq128305 eq116663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116663 eq128305
  have eq128726 : False := by grind
  exact eq128726

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_x_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq395 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq395
    | (have j0 := eq395 X0 X1
       grind)
    | exact resolve eq395 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq698 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq412 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq412
    | exact resolve eq412 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq712 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq698 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq698
    | (have j0 := eq698 X0 X1
       grind)
    | exact resolve eq698 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq698
  have eq719 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq712 X0 X1
       have j1 := eq90 X1 X0
       grind)
    | (have r₁ := eq712 X1 X0
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq712 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq712 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq712
  have eq722 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq719 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq719
    | exact resolve eq719 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq719 (σ X1) X0
       grind)
    | exact superpose eq719 eq15
    | (have j1 := eq719 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq769 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq722 (τ X0) X1
       grind)
    | exact superpose eq722 eq19
    | (have j1 := eq722 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq722
  have eq862 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq769 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq769
    | exact resolve eq769 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq904 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq862 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq862
    | (have j0 := eq862 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq862 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq1085 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq736 x y
       grind)
    | exact superpose eq736 eq16
    | (have j1 := eq736 x y
       grind)
    | exact resolve eq16 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq1101 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1085
       have i₂ := eq904 x y
       grind)
    | exact superpose eq904 eq1085
    | (have j1 := eq904 (σ x) (σ y)
       grind)
    | (have r₁ := eq1085
       have r₂ := eq904 x y
       grind)
    | (have r₁ := eq1085
       have r₂ := eq904 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1085
       have r₂ := eq904 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1085 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904 eq1085
  have eq1102 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1101
  have eq1105 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1102
       grind)
    | exact superpose eq1102 eq16
    | exact resolve eq16 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1106 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1105
       have r₂ := eq76 x
       grind)
    | exact resolve eq1105 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1107 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1106
       grind)
    | exact superpose eq1106 eq16
    | exact resolve eq16 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1108 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1106
       grind)
    | exact superpose eq1106 eq10
    | exact resolve eq10 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq1154 : x = y := by
    first
    | (have i₁ := eq1108
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1108
    | exact resolve eq1108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1155 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1107
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq1107
    | exact resolve eq1107 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq1107
  have eq1156 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1155
       have i₂ := eq1154
       grind)
    | exact superpose eq1154 eq1155
    | exact resolve eq1155 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154 eq1155
  have eq1157 : False := by grind
  exact eq1157

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_y_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq268 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq268 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq274 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq273 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq377 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq274 X1 X0
       grind)
    | exact superpose eq274 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq274 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq274 X0 X1
       grind)
    | exact resolve eq13 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq274 (σ x) (σ y)
       grind)
    | exact superpose eq274 eq16
    | (have j1 := eq274 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq377 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq386 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq381
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq381
    | exact resolve eq381 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq387 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq385 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq385 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq385 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq412 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq387 X1 (τ X0)
       grind)
    | exact superpose eq387 eq17
    | (have j1 := eq387 X1 (τ X0)
       grind)
    | exact resolve eq17 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq418 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq387 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1001 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq412 X1 (τ X0)
       grind)
    | exact superpose eq412 eq18
    | (have j1 := eq412 X1 (τ X0)
       grind)
    | exact resolve eq18 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq412
  have eq1006 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1001 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1001
    | (have j0 := eq1001 X0 X1
       grind)
    | exact resolve eq1001 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1024 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1006 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1006
    | (have j0 := eq1006 X0 X1
       grind)
    | exact resolve eq1006 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq1029 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1024 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1024
    | (have j0 := eq1024 X0 X1
       grind)
    | exact resolve eq1024 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1086 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1029 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1029
    | (have j0 := eq1029 X1 (σ X0)
       grind)
    | exact resolve eq1029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1354 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (σ (M.op X0 (τ X1))) = (M.op (σ X0) X1) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1086 X0 X0
       have i₂ := eq387 X0 (σ X0)
       grind)
    | exact superpose eq387 eq1086
    | (have j0 := eq1086 X0 X1
       have j1 := eq387 X1 (σ X0)
       grind)
    | exact resolve eq1086 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq1086
  have eq1390 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ (M.op X0 (τ X1))) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1354 X0 X1
       have j1 := eq418 (σ X0) X1
       grind)
    | (have r₁ := eq1354 X0 X1
       have r₂ := eq418 (σ X0) X1
       grind)
    | exact resolve eq1354 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418 eq1354
  have eq1581 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq1390 X1 (σ X0)
       grind)
    | exact superpose eq1390 eq22
    | (have j1 := eq1390 X1 (σ X0)
       grind)
    | exact resolve eq22 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1390
  have eq1588 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1581 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1581
    | (have j0 := eq1581 X0 X1
       grind)
    | exact resolve eq1581 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581
  have eq1608 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1588 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1588
    | (have j0 := eq1588 X0 X1
       grind)
    | exact resolve eq1588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588
  have eq1619 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1608 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1608
    | (have j0 := eq1608 X0 X1
       grind)
    | exact resolve eq1608 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608
  have eq1706 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1619 y x
       grind)
    | exact superpose eq1619 eq16
    | (have j1 := eq1619 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1619 y x
       grind)
    | exact resolve eq16 eq1619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619
  have eq1731 : y = (k x y) := by grind
  clear eq1706
  have eq2022 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq386
       have i₂ := eq274 x y
       grind)
    | exact superpose eq274 eq386
    | (have j1 := eq274 x y
       grind)
    | exact resolve eq386 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2025 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq2022
  have eq2026 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2025
       have i₂ := eq1731
       grind)
    | exact superpose eq1731 eq2025
    | exact resolve eq2025 eq1731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025
  have eq2027 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2026
       have i₂ := eq1731
       grind)
    | exact superpose eq1731 eq2026
    | exact resolve eq2026 eq1731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2026
  have eq2028 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq386
       have i₂ := eq2027
       grind)
    | exact superpose eq2027 eq386
    | exact resolve eq386 eq2027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq2027
  have eq2037 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2028
  have eq2038 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2037
       have i₂ := eq1731
       grind)
    | exact superpose eq1731 eq2037
    | exact resolve eq2037 eq1731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2037
  have eq2039 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2038
  have eq2041 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2039
       grind)
    | exact superpose eq2039 eq16
    | exact resolve eq16 eq2039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039
  have eq2062 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2041
       have i₂ := eq274 x y
       grind)
    | exact superpose eq274 eq2041
    | (have j1 := eq274 x y
       grind)
    | exact resolve eq2041 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq2065 : (M.op x y) = (k x y) := by grind
  clear eq2062
  have eq2067 : y = (M.op x y) := by
    first
    | (have i₁ := eq2065
       have i₂ := eq1731
       grind)
    | exact superpose eq1731 eq2065
    | exact resolve eq2065 eq1731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1731 eq2065
  have eq2068 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2041
       have i₂ := eq2067
       grind)
    | exact superpose eq2067 eq2041
    | exact resolve eq2041 eq2067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041 eq2067
  have eq2079 : False := by grind
  exact eq2079

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_y_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq365 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq369 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq365 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq365
    | (have j0 := eq365 (σ X0) (σ X1)
       grind)
    | exact resolve eq365 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq369 X1 X0
       have i₂ := eq365 X1 X0
       grind)
    | exact superpose eq365 eq369
    | (have j0 := eq369 X1 X0
       have j1 := eq365 (σ X1) (σ X0)
       grind)
    | exact resolve eq369 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq614 x y
       grind)
    | exact superpose eq614 eq16
    | (have j1 := eq614 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq614 x y
       grind)
    | exact resolve eq16 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq832 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq821
  have eq856 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq832
       grind)
    | exact superpose eq832 eq16
    | exact resolve eq16 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq857 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq832
       grind)
    | exact superpose eq832 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq832
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq832
       grind)
    | exact resolve eq13 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq858 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq832
       grind)
    | exact superpose eq832 eq12
    | exact resolve eq12 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq859 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq857
  have eq861 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq858
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq858
    | exact resolve eq858 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq862 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq859
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq859
    | exact resolve eq859 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq863 : (σ (M.op x y)) = (σ x) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq365 eq861
    | (have j1 := eq365 y x
       grind)
    | exact resolve eq861 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq864 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq365 eq862
    | (have j1 := eq365 y x
       grind)
    | exact resolve eq862 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq862
  have eq866 : x = (M.op x y) := by grind
  clear eq856 eq863 eq864
  have eq868 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq866
       grind)
    | exact superpose eq866 eq16
    | exact resolve eq16 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : x ≠ x ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq866
       grind)
    | exact superpose eq866 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq866
       grind)
    | exact resolve eq13 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq870 : x ≠ y ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq866
       grind)
    | exact superpose eq866 eq12
    | exact resolve eq12 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq871 : x = y ∨ x = (k y x) := by grind
  clear eq869
  have eq872 : x = (k y x) := by
    first
    | (have r₁ := eq871
       have r₂ := eq870
       grind)
    | exact resolve eq871 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870 eq871
  have eq876 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq369 y x
       have i₂ := eq872
       grind)
    | exact superpose eq872 eq369
    | (have j0 := eq369 y x
       grind)
    | exact resolve eq369 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq872
  have eq879 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq876
  have eq883 : False := by grind
  exact eq883

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq17
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
  clear eq22
  have eq402 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq403 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq402 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq402
    | (have j0 := eq402 (σ X0) (σ X1)
       grind)
    | exact resolve eq402 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq858 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq403 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq403 X0 X1
       grind)
    | exact superpose eq403 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq403 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq403 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq403 X0 X1
       grind)
    | exact resolve eq13 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq862 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq858 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq867 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq862 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq862 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq862 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq877 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq867 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq867
    | (have j0 := eq867 X0 X1
       grind)
    | exact resolve eq867 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq878 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq877 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq892 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq878 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq878
    | exact resolve eq878 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq912 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq892 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq892
    | exact resolve eq892 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq925 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq912 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq912
    | exact resolve eq912 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq936 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq925 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq925
    | exact resolve eq925 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq943 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq878 X0 X1
       have i₂ := eq936 X1 X0
       grind)
    | exact superpose eq936 eq878
    | exact resolve eq878 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878 eq936
  have eq979 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq943 x y
       grind)
    | exact superpose eq943 eq16
    | (have r₁ := eq16
       have r₂ := eq943 x y
       grind)
    | exact resolve eq16 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq991 : False := by grind
  exact eq991

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X1) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq62 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) ≠ X0 ∨ (k X0 (M.op (M.op (M.op X0 X0) X1) X1)) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X0 X0) X1) X1)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op (M.op (M.op X0 X0) X1) X1)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq92 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
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
  have eq746 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq90 x y
       grind)
    | exact superpose eq90 eq16
    | (have j1 := eq90 x y
       grind)
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq4492 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq62 x x
       have i₂ := eq63 x x
       grind)
    | exact superpose eq63 eq62
    | (have j1 := eq63 X0 x
       grind)
    | (have r₁ := eq62 x x
       have r₂ := eq63 x x
       grind)
    | exact resolve eq62 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq63
  have eq4494 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4492 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4492
  have eq4495 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4494 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4494
  have eq4569 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4495 (σ X0)
       grind)
    | exact superpose eq4495 eq15
    | exact resolve eq15 eq4495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4588 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4569 X0
       have i₂ := eq4495 X0
       grind)
    | exact superpose eq4495 eq4569
    | exact resolve eq4569 eq4495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4495 eq4569
  have eq8990 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq92 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92
    | exact resolve eq92 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq9066 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8990 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8990
    | (have j0 := eq8990 X0 X1
       grind)
    | exact resolve eq8990 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8990
  have eq27116 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq746
       have i₂ := eq9066 x y
       grind)
    | exact superpose eq9066 eq746
    | (have j1 := eq9066 (σ x) (σ y)
       grind)
    | (have r₁ := eq746
       have r₂ := eq9066 x y
       grind)
    | (have r₁ := eq746
       have r₂ := eq9066 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq746
       have r₂ := eq9066 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq746 eq9066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27117 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq27116
  have eq34716 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27117
       grind)
    | exact superpose eq27117 eq16
    | exact resolve eq16 eq27117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27117
  have eq34717 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq34716
       have r₂ := eq4588 x
       grind)
    | exact resolve eq34716 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34716
  have eq34719 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq34717
       grind)
    | exact superpose eq34717 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq34717
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq34717
       grind)
    | exact resolve eq12 eq34717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34717
  have eq34720 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq34719
  have eq34721 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq746
       have i₂ := eq34720
       grind)
    | exact superpose eq34720 eq746
    | exact resolve eq746 eq34720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746 eq34720
  have eq34722 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq34721
  have eq34723 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq34722
  have eq34728 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq34723
       grind)
    | exact superpose eq34723 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq34723
       grind)
    | exact resolve eq12 eq34723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34723
  have eq34729 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq34728
  have eq34733 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34729
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq34729
    | exact resolve eq34729 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34729
  have eq34831 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34733
       grind)
    | exact superpose eq34733 eq16
    | exact resolve eq16 eq34733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34733
  have eq34865 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq34831
       have i₂ := eq9066 x y
       grind)
    | exact superpose eq9066 eq34831
    | (have j1 := eq9066 x y
       grind)
    | (have r₁ := eq34831
       have r₂ := eq9066 x y
       grind)
    | (have r₁ := eq34831
       have r₂ := eq9066 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq34831
       have r₂ := eq9066 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq34831 eq9066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9066
  have eq34866 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq34865
  have eq34870 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34866
       grind)
    | exact superpose eq34866 eq16
    | exact resolve eq16 eq34866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34866
  have eq34871 : y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq34870
       have r₂ := eq4588 x
       grind)
    | exact resolve eq34870 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34870
  have eq34872 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq34871
       grind)
    | exact superpose eq34871 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq34871
       grind)
    | exact resolve eq12 eq34871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34871
  have eq34875 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq34872
  have eq34876 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34831
       have i₂ := eq34875
       grind)
    | exact superpose eq34875 eq34831
    | exact resolve eq34831 eq34875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34831 eq34875
  have eq34880 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq34876
  have eq34881 : (σ x) = (σ y) := by grind
  clear eq34880
  have eq34882 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34881
       grind)
    | exact superpose eq34881 eq16
    | exact resolve eq16 eq34881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34883 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq34881
       grind)
    | exact superpose eq34881 eq10
    | exact resolve eq10 eq34881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34881
  have eq34964 : x = y := by
    first
    | (have i₁ := eq34883
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq34883
    | exact resolve eq34883 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34883
  have eq34965 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq34882
       have i₂ := eq4588 x
       grind)
    | exact superpose eq4588 eq34882
    | exact resolve eq34882 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4588 eq34882
  have eq34973 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq34965
       have i₂ := eq34964
       grind)
    | exact superpose eq34964 eq34965
    | exact resolve eq34965 eq34964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34964 eq34965
  have eq34974 : False := by grind
  exact eq34974
