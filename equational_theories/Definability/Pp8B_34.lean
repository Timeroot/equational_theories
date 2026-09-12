import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_x_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq92 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | (have i₁ := eq77 X0
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq77
    | (have j1 := eq14 (M.op X0 X0) (σ (M.op X1 X1))
       grind)
    | exact resolve eq77 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq415 X0 X1
       have j1 := eq92 X1 X0
       grind)
    | (have r₁ := eq415 X1 X0
       have r₂ := eq92 X0 X1
       grind)
    | (have r₁ := eq415 (M.op X1 X1) (M.op X0 X0)
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq415 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq415
  have eq429 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq418 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq418
    | exact resolve eq418 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq418 (σ X1) X0
       grind)
    | exact superpose eq418 eq15
    | (have j1 := eq418 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq469 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq429 (τ X0) X1
       grind)
    | exact superpose eq429 eq19
    | (have j1 := eq429 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq429
  have eq596 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq469 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq469
    | exact resolve eq469 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq634 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq596 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq596
    | (have j0 := eq596 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq596 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq815 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq440 x y
       grind)
    | exact superpose eq440 eq16
    | (have j1 := eq440 x y
       grind)
    | exact resolve eq16 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq830 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq815
       have i₂ := eq634 x y
       grind)
    | exact superpose eq634 eq815
    | (have j1 := eq634 (σ x) (σ y)
       grind)
    | (have r₁ := eq815
       have r₂ := eq634 x y
       grind)
    | (have r₁ := eq815
       have r₂ := eq634 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq815
       have r₂ := eq634 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq815 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634 eq815
  have eq831 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq830
  have eq834 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq831
       grind)
    | exact superpose eq831 eq16
    | exact resolve eq16 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq835 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq834
       have r₂ := eq77 x
       grind)
    | exact resolve eq834 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq836 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq835
       grind)
    | exact superpose eq835 eq16
    | exact resolve eq16 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq837 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq835
       grind)
    | exact superpose eq835 eq10
    | exact resolve eq10 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq879 : x = y := by
    first
    | (have i₁ := eq837
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq837
    | exact resolve eq837 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq880 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq836
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq836
    | exact resolve eq836 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq836
  have eq881 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq880
       have i₂ := eq879
       grind)
    | exact superpose eq879 eq880
    | exact resolve eq880 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879 eq880
  have eq882 : False := by grind
  exact eq882

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_pyx_pyx_pxx_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq21 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X1
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
  have eq32 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq36 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq32 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq33 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq33 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq93 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq97 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       have j1 := eq47 X1 X0
       grind)
    | (have r₁ := eq93 X1 X0
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq93 X0 X0
       have r₂ := eq47 X0 X0
       grind)
    | exact resolve eq93 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq93
  have eq230 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
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
  have eq237 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq230 X0 X1
       have i₂ := eq97 X1 X0
       grind)
    | exact superpose eq97 eq230
    | exact resolve eq230 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq230
  have eq240 : False := by grind
  exact eq240

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_pyx_pyx_pxy_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq57
  have eq80 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq92 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq66 X1
       grind)
    | exact superpose eq66 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq86
  have eq184 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq13
    | (have j0 := eq13 (σ X1) X1
       have j1 := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq195 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq200 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq195 X0 X1
       have j1 := eq80 X1 (σ X0)
       grind)
    | (have r₁ := eq195 X0 X0
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq195 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq195
  have eq211 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq200 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq200 X0 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq200 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq218 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq211 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq211
    | (have j0 := eq211 X0 X1
       grind)
    | exact resolve eq211 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq219 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq218 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq223 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq219 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq219
    | exact resolve eq219 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq219 x y
       grind)
    | exact superpose eq219 eq16
    | exact resolve eq16 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq292 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq223 X0 (τ X1)
       grind)
    | exact superpose eq223 eq17
    | exact resolve eq17 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq223
  have eq310 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq292 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq292
    | exact resolve eq292 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq318 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq310
    | exact resolve eq310 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq335 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq234
       have i₂ := eq318 x y
       grind)
    | exact superpose eq318 eq234
    | exact resolve eq234 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq318
  have eq336 : False := by grind
  exact eq336

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_pyx_x_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 := by
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
  clear eq19
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
  have eq46 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq74 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq193 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq3719 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq78 X1 X0
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq78 X0 (σ X0)
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3744 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq78 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3745 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3744 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3744
  have eq3746 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3719 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3719
  have eq3747 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3746 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3746
  have eq3749 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3745 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3745
    | (have j0 := eq3745 X0
       grind)
    | exact resolve eq3745 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3745
  have eq3793 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq3749 X0
       grind)
    | exact superpose eq3749 eq46
    | (have j1 := eq3749 X0
       grind)
    | exact resolve eq46 eq3749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq3749
  have eq3813 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3793 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3793
    | (have j0 := eq3793 X0
       grind)
    | exact resolve eq3793 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3793
  have eq3814 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3813 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3813
  have eq3816 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3814 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3814
    | exact resolve eq3814 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3841 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq3814 X0
       grind)
    | exact superpose eq3814 eq11
    | exact resolve eq11 eq3814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3814
  have eq3899 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3816 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq3816
    | exact resolve eq3816 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816
  have eq4111 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3899 X0
       grind)
    | exact superpose eq3899 eq11
    | exact resolve eq11 eq3899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4215 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4111 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4111
    | exact resolve eq4111 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4111
  have eq4273 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq4215 (τ X0)
       grind)
    | exact superpose eq4215 eq34
    | exact resolve eq34 eq4215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4325 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4273 X0
       have i₂ := eq3899 X0
       grind)
    | exact superpose eq3899 eq4273
    | exact resolve eq4273 eq3899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3899 eq4273
  have eq4815 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    grind
  have eq4847 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4815 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq4815
    | exact resolve eq4815 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4815
  have eq4882 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4847 X0
       have i₂ := eq4215 X0
       grind)
    | exact superpose eq4215 eq4847
    | exact resolve eq4847 eq4215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4847
  have eq4896 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq4882
  have eq27259 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ X1)
       have i₂ := eq3747 (σ X0) X1
       grind)
    | exact superpose eq3747 eq30
    | (have j1 := eq3747 (σ X0) X1
       grind)
    | exact resolve eq30 eq3747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3747
  have eq27348 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq27259 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq27259
    | (have j0 := eq27259 X0 X1
       grind)
    | exact resolve eq27259 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27259
  have eq27425 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq27348 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27348
    | (have j0 := eq27348 X0 X1
       grind)
    | exact resolve eq27348 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27348
  have eq27493 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq27425 X0 X1
       have i₂ := eq3841 X0
       grind)
    | exact superpose eq3841 eq27425
    | (have j0 := eq27425 X0 X1
       grind)
    | exact resolve eq27425 eq3841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27425
  have eq27539 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq27493 X0 X1
       have i₂ := eq4215 X0
       grind)
    | exact superpose eq4215 eq27493
    | (have j0 := eq27493 X0 X1
       grind)
    | exact resolve eq27493 eq4215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27493
  have eq27578 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27539 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27539
    | (have j0 := eq27539 X0 X1
       grind)
    | exact resolve eq27539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27539
  have eq30101 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (σ (M.op X1 X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq27578 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27578
    | (have j0 := eq27578 X1 (τ X0)
       grind)
    | exact resolve eq27578 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30184 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq27578 X0 X1
       grind)
    | exact superpose eq27578 eq11
    | (have j1 := eq27578 X0 X1
       grind)
    | exact resolve eq11 eq27578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27578
  have eq30757 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30101 X0 (τ X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq30101
    | (have j0 := eq30101 X1 (τ X0)
       grind)
    | exact resolve eq30101 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq30101
  have eq30948 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30757 X0 X1
       have i₂ := eq4325 X0
       grind)
    | exact superpose eq4325 eq30757
    | (have j0 := eq30757 X0 X1
       grind)
    | exact resolve eq30757 eq4325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4325 eq30757
  have eq31034 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30948 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq30948
    | (have j0 := eq30948 X0 X1
       grind)
    | exact resolve eq30948 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30948
  have eq31108 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31034 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31034
    | (have j0 := eq31034 X0 X1
       grind)
    | exact resolve eq31034 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31034
  have eq31484 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq31108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31108
  have eq33491 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30184 y x
       grind)
    | exact superpose eq30184 eq16
    | (have j1 := eq30184 y x
       grind)
    | exact resolve eq16 eq30184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30184
  have eq34370 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq33491
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq33491
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq33491 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33491
  have eq34373 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq34370
  have eq34374 : y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq34373
  have eq34388 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ y) = (τ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31484 y x
       have i₂ := eq34374
       grind)
    | exact superpose eq34374 eq31484
    | (have j0 := eq31484 y x
       grind)
    | exact resolve eq31484 eq34374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31484
  have eq34389 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ y) = (τ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq34388
  have eq34390 : x = (M.op y y) ∨ (τ y) = (τ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq34389
  have eq34719 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4896 y
       have i₂ := eq34390
       grind)
    | exact superpose eq34390 eq4896
    | exact resolve eq4896 eq34390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34390
  have eq34749 : (σ x) = (σ (M.op y y)) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have r₁ := eq34719
       have r₂ := eq16
       grind)
    | exact resolve eq34719 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34719
  have eq35061 : (M.op y y) = (τ (σ x)) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq34749
       grind)
    | exact superpose eq34749 eq10
    | exact resolve eq10 eq34749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34749
  have eq35204 : x = (M.op y y) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq35061
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq35061
    | exact resolve eq35061 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35061
  have eq35309 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq4896 y
       have i₂ := eq35204
       grind)
    | exact superpose eq35204 eq4896
    | exact resolve eq4896 eq35204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35204
  have eq35339 : (τ y) = (τ (k y x)) := by
    first
    | (have r₁ := eq35309
       have r₂ := eq16
       grind)
    | exact resolve eq35309 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35309
  have eq35649 : (k y x) = (σ (τ y)) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq35339
       grind)
    | exact superpose eq35339 eq11
    | exact resolve eq11 eq35339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35339
  have eq35825 : y = (k y x) := by
    first
    | (have i₁ := eq35649
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq35649
    | exact resolve eq35649 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35649
  have eq35895 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq193 x y
       have i₂ := eq35825
       grind)
    | exact superpose eq35825 eq193
    | (have j0 := eq193 x y
       grind)
    | exact resolve eq193 eq35825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq35825
  have eq35901 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq35895
  have eq35904 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35901
       have i₂ := eq3841 y
       grind)
    | exact superpose eq3841 eq35901
    | exact resolve eq35901 eq3841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3841 eq35901
  have eq35907 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq35904
       have i₂ := eq4215 y
       grind)
    | exact superpose eq4215 eq35904
    | exact resolve eq35904 eq4215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4215 eq35904
  have eq39765 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35907
       grind)
    | exact superpose eq35907 eq16
    | exact resolve eq16 eq35907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35907
  have eq39834 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39765
       have i₂ := eq34374
       grind)
    | exact superpose eq34374 eq39765
    | exact resolve eq39765 eq34374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34374 eq39765
  have eq39835 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq39834
  have eq39836 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq39835
  have eq40409 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4896 y
       have i₂ := eq39836
       grind)
    | exact superpose eq39836 eq4896
    | exact resolve eq4896 eq39836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39836
  have eq40439 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq40409
       have r₂ := eq16
       grind)
    | exact resolve eq40409 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40409
  have eq40465 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq40439
       grind)
    | exact superpose eq40439 eq10
    | exact resolve eq10 eq40439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40439
  have eq40610 : x = (M.op y y) := by
    first
    | (have i₁ := eq40465
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq40465
    | exact resolve eq40465 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40465
  have eq41291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4896 y
       have i₂ := eq40610
       grind)
    | exact superpose eq40610 eq4896
    | exact resolve eq4896 eq40610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4896 eq40610
  have eq41321 : False := by grind
  exact eq41321

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_pxy_y_pxy_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq406 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq406 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq429 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq427 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq427 (M.op X0 X1) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq427 (k X0 X1) (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq427 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq427 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq432 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq424
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq424 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq450 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq428 (M.op X0 X1) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq428 X0 (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq428 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq428 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq455 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq432
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq432
    | exact resolve eq432 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq456 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq450 X0 X1
       have j1 := eq429 X1 X0
       grind)
    | (have r₁ := eq450 X0 X1
       have r₂ := eq429 X0 X1
       grind)
    | (have r₁ := eq450 X1 X0
       have r₂ := eq429 X0 X1
       grind)
    | (have r₁ := eq450 X1 X1
       have r₂ := eq429 (k X1 X1) X1
       grind)
    | exact resolve eq450 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq450
  have eq596 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq456 X1 (τ X0)
       grind)
    | exact superpose eq456 eq17
    | (have j1 := eq456 X1 (τ X0)
       grind)
    | exact resolve eq17 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq603 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq456 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq852 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq596 X1 (τ X0)
       grind)
    | exact superpose eq596 eq18
    | (have j1 := eq596 X1 (τ X0)
       grind)
    | exact resolve eq18 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq596
  have eq857 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq852 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq852
    | (have j0 := eq852 X0 X1
       grind)
    | exact resolve eq852 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq870 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq857 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq857
    | (have j0 := eq857 X0 X1
       grind)
    | exact resolve eq857 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq873 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq870 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq870
    | (have j0 := eq870 X0 X1
       grind)
    | exact resolve eq870 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq927 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq873 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq873
    | (have j0 := eq873 X1 (σ X0)
       grind)
    | exact resolve eq873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq1308 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (σ (M.op X0 (τ X1))) = (M.op (σ X0) X1) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq927 X0 X0
       have i₂ := eq456 X0 (σ X0)
       grind)
    | exact superpose eq456 eq927
    | (have j0 := eq927 X0 X1
       have j1 := eq456 X1 (σ X0)
       grind)
    | exact resolve eq927 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq927
  have eq1338 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ (M.op X0 (τ X1))) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1308 X0 X1
       have j1 := eq603 (σ X0) X1
       grind)
    | (have r₁ := eq1308 X0 X1
       have r₂ := eq603 (σ X0) X1
       grind)
    | exact resolve eq1308 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq1308
  have eq1505 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ (M.op X1 (τ (σ X0)))) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq1338 X1 (σ X0)
       grind)
    | exact superpose eq1338 eq22
    | (have j1 := eq1338 X1 (σ X0)
       grind)
    | exact resolve eq22 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1338
  have eq1512 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ (M.op X1 (τ (σ X0)))) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1505 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1505
    | (have j0 := eq1505 X0 X1
       grind)
    | exact resolve eq1505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505
  have eq1528 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ (M.op X1 (τ (σ X0)))) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1512 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1512
    | (have j0 := eq1512 X0 X1
       grind)
    | exact resolve eq1512 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512
  have eq1537 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1528 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1528
    | (have j0 := eq1528 X0 X1
       grind)
    | exact resolve eq1528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528
  have eq1621 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1537 y x
       grind)
    | exact superpose eq1537 eq16
    | (have j1 := eq1537 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1537 y x
       grind)
    | exact resolve eq16 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537
  have eq1645 : y = (k x y) := by grind
  clear eq1621
  have eq1918 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq455
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq455
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq455 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1919 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq1918
  have eq1920 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1919
       have r₂ := eq12 x y
       grind)
    | exact resolve eq1919 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919
  have eq1921 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1920
       have i₂ := eq1645
       grind)
    | exact superpose eq1645 eq1920
    | exact resolve eq1920 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920
  have eq1922 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1921
       have i₂ := eq1645
       grind)
    | exact superpose eq1645 eq1921
    | exact resolve eq1921 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq1923 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq455
       have i₂ := eq1922
       grind)
    | exact superpose eq1922 eq455
    | exact resolve eq455 eq1922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq1922
  have eq1935 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1923
  have eq1936 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1935
       have i₂ := eq1645
       grind)
    | exact superpose eq1645 eq1935
    | exact resolve eq1935 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1935
  have eq1937 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1936
  have eq1939 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1937
       grind)
    | exact superpose eq1937 eq16
    | exact resolve eq16 eq1937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937
  have eq1968 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1939
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1939
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq1939 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1969 : x = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq1968
  have eq1971 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1969
       have r₂ := eq12 x y
       grind)
    | exact resolve eq1969 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969
  have eq1972 : y = (M.op x y) := by
    first
    | (have i₁ := eq1971
       have i₂ := eq1645
       grind)
    | exact superpose eq1645 eq1971
    | exact resolve eq1971 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645 eq1971
  have eq1973 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1939
       have i₂ := eq1972
       grind)
    | exact superpose eq1972 eq1939
    | exact resolve eq1939 eq1972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939 eq1972
  have eq1987 : False := by grind
  exact eq1987

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pxy_pxx_pxy_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X0))) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq62 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X0))) (M.op X0 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op X0 (M.op X1 X0)))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 (σ X1) (M.op X0 (σ X1))
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq156 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X0))) X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq62
  have eq163 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq156 X0 x
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq156
    | (have j0 := eq156 X0 x
       grind)
    | exact resolve eq156 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq164 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq163 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq163 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq163 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq169 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq164 (σ X0)
       grind)
    | exact superpose eq164 eq15
    | exact resolve eq15 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq169 X0
       have i₂ := eq164 X0
       grind)
    | exact superpose eq164 eq169
    | exact resolve eq169 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq169
  have eq810 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq141 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq10113 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X1)
       have i₂ := eq138 X0 X1
       grind)
    | exact superpose eq138 eq12
    | (have j1 := eq138 X1 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq138 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq138 (M.op X0 (σ X1)) X1
       grind)
    | exact resolve eq12 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq10131 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = X1 ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq10113 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10113
  have eq11381 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10131 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10131
    | exact resolve eq10131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10131
  have eq11498 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11381 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq11381
    | (have j0 := eq11381 X0 X1
       grind)
    | exact resolve eq11381 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq11381
  have eq11530 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq11498 X1 (σ X0)
       grind)
    | exact superpose eq11498 eq29
    | (have j1 := eq11498 (k (σ X0) X1) X1
       grind)
    | exact resolve eq29 eq11498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq11533 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq11498 X1 X0
       grind)
    | exact superpose eq11498 eq11
    | (have j1 := eq11498 (k X0 X1) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq11498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11498
  have eq11662 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11533 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq11533
    | (have j0 := eq11533 X0 X1
       grind)
    | exact resolve eq11533 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11533
  have eq11746 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq11662 (τ X0) X1
       grind)
    | exact superpose eq11662 eq18
    | (have j1 := eq11662 (τ X0) X1
       grind)
    | exact resolve eq18 eq11662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq11662
  have eq12067 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq11530 X1 (σ X0)
       grind)
    | exact superpose eq11530 eq23
    | (have j1 := eq11530 X0 (σ X1)
       grind)
    | exact resolve eq23 eq11530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11530
  have eq12137 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12067 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq12067
    | (have j0 := eq12067 X0 X1
       grind)
    | exact resolve eq12067 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12067
  have eq12172 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12137 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12137
    | (have j0 := eq12137 X0 X1
       grind)
    | exact resolve eq12137 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12137
  have eq12181 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12172 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12172
    | (have j0 := eq12172 X0 X1
       grind)
    | exact resolve eq12172 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12172
  have eq12185 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11746 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11746
    | exact resolve eq11746 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11746
  have eq12276 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12185 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq12185
    | (have j0 := eq12185 X0 X1
       grind)
    | exact resolve eq12185 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12185
  have eq12478 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq12181 X1 X0
       grind)
    | exact superpose eq12181 eq11
    | (have j1 := eq12181 X1 X0
       grind)
    | exact resolve eq11 eq12181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12181
  have eq13631 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12478 x y
       grind)
    | exact superpose eq12478 eq16
    | (have j1 := eq12478 x y
       grind)
    | exact resolve eq16 eq12478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12478
  have eq13686 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13631
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq13631
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq13631
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq13631
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq13631 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13687 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq13631
       have i₂ := eq12276 x y
       grind)
    | exact superpose eq12276 eq13631
    | (have j1 := eq12276 x y
       grind)
    | (have r₁ := eq13631
       have r₂ := eq12276 x y
       grind)
    | (have r₁ := eq13631
       have r₂ := eq12276 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq13631
       have r₂ := eq12276 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq13631 eq12276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12276 eq13631
  have eq13690 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13687
  have eq13691 : x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq13690
  have eq13692 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13686
  have eq13693 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq13692
  have eq13697 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13691
       grind)
    | exact superpose eq13691 eq16
    | exact resolve eq16 eq13691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13691
  have eq13698 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq13697
       have r₂ := eq176 x
       grind)
    | exact resolve eq13697 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13697
  have eq13703 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq810 x y
       have i₂ := eq13698
       grind)
    | exact superpose eq13698 eq810
    | (have j0 := eq810 x y
       grind)
    | exact resolve eq810 eq13698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq13698
  have eq13716 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13703
  have eq13717 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq13716
  have eq13722 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13693
       grind)
    | exact superpose eq13693 eq16
    | exact resolve eq16 eq13693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13693
  have eq13723 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq13722
       have r₂ := eq176 x
       grind)
    | exact resolve eq13722 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13722
  have eq13738 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13717
       grind)
    | exact superpose eq13717 eq16
    | exact resolve eq16 eq13717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13717
  have eq13785 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13738
       have i₂ := eq13723
       grind)
    | exact superpose eq13723 eq13738
    | exact resolve eq13738 eq13723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13723 eq13738
  have eq13786 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq13785
  have eq13787 : (σ x) = (σ y) := by grind
  clear eq13786
  have eq13788 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13787
       grind)
    | exact superpose eq13787 eq16
    | exact resolve eq16 eq13787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13789 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq13787
       grind)
    | exact superpose eq13787 eq10
    | exact resolve eq10 eq13787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13787
  have eq13861 : x = y := by
    first
    | (have i₁ := eq13789
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13789
    | exact resolve eq13789 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13789
  have eq13862 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq13788
       have i₂ := eq176 x
       grind)
    | exact superpose eq176 eq13788
    | exact resolve eq13788 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq13788
  have eq13865 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq13862
       have i₂ := eq13861
       grind)
    | exact superpose eq13861 eq13862
    | exact resolve eq13862 eq13861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13861 eq13862
  have eq13866 : False := by grind
  exact eq13866

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyx_pyx_pxx_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
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
  have eq34 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq38 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X1
       grind)
    | (have r₁ := eq34 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq41
  have eq47 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq38 X1 X0
       grind)
    | (have r₁ := eq44 X1 X1
       have r₂ := eq38 X0 X1
       grind)
    | exact resolve eq44 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq44
  have eq134 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq139 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq134 X0 X1
       have j1 := eq46 X1 X0
       grind)
    | (have r₁ := eq134 X1 X0
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq134 X0 X0
       have r₂ := eq46 X0 X0
       grind)
    | exact resolve eq134 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq134
  have eq265 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq139 (σ X1) (σ X0)
       grind)
    | exact superpose eq139 eq15
    | exact resolve eq15 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq265 X0 X1
       have i₂ := eq139 X1 X0
       grind)
    | exact superpose eq139 eq265
    | exact resolve eq265 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq265
  have eq275 : False := by grind
  exact eq275

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pxy_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
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
  have eq836 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq839 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq5047 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq836 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq21196 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) X1) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) X0
       have i₂ := eq839 X0 X1
       grind)
    | exact superpose eq839 eq12
    | (have j1 := eq839 X1 X0
       grind)
    | (have r₁ := eq12 (τ X1) X0
       have r₂ := eq839 X0 X1
       grind)
    | exact resolve eq12 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq21229 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq21196 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21196
  have eq31288 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5047 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq5047
    | (have j0 := eq5047 (τ X1) (τ X0)
       grind)
    | exact resolve eq5047 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31414 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31288 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq31288
    | (have j0 := eq31288 X0 X1
       grind)
    | exact resolve eq31288 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31288
  have eq31472 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31414 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31414
    | (have j0 := eq31414 X0 X1
       grind)
    | exact resolve eq31414 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31414
  have eq31526 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31472 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31472
    | (have j0 := eq31472 X0 X1
       grind)
    | exact resolve eq31472 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31472
  have eq31563 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31526 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31526
    | (have j0 := eq31526 X0 X1
       grind)
    | exact resolve eq31526 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31526
  have eq31585 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31563 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31563
    | (have j0 := eq31563 X0 X1
       grind)
    | exact resolve eq31563 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31563
  have eq31599 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31585 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq31585
    | (have j0 := eq31585 X0 X1
       grind)
    | exact resolve eq31585 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31585
  have eq32893 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21229 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21229
    | exact resolve eq21229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21229
  have eq33068 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32893 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq32893
    | (have j0 := eq32893 X0 X1
       grind)
    | exact resolve eq32893 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32893
  have eq33141 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq33068 X1 X0
       grind)
    | exact superpose eq33068 eq10
    | (have j1 := eq33068 X0 X1
       grind)
    | exact resolve eq10 eq33068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33068
  have eq33328 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33141 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq33141
    | (have j0 := eq33141 X0 X1
       grind)
    | exact resolve eq33141 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33141
  have eq33388 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq33328 (σ X0) X1
       grind)
    | exact superpose eq33328 eq22
    | (have j1 := eq33328 (σ X0) X1
       grind)
    | exact resolve eq22 eq33328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33328
  have eq35795 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33388 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33388
    | exact resolve eq33388 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33388
  have eq35949 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35795 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq35795
    | (have j0 := eq35795 X0 X1
       grind)
    | exact resolve eq35795 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35795
  have eq35973 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X0 X1))) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35949 (τ X0) (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq35949
    | (have j0 := eq35949 (τ X0) (τ X1)
       grind)
    | exact resolve eq35949 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35949
  have eq1065152 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (τ X0)
       have i₂ := eq35973 X0 X1
       grind)
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq35973 X0 X1
       grind)
    | exact superpose eq35973 eq13
    | (have j0 := eq13 (τ X1) (τ X0)
       have j1 := eq35973 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq35973 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) (τ X0)
       have r₂ := eq35973 X0 X1
       grind)
    | exact resolve eq13 eq35973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35973
  have eq1065168 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X0) (τ X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1065152 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065152
  have eq1065185 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1065168 X0 X1
       have j1 := eq12 (τ X1) (τ X0)
       grind)
    | (have r₁ := eq1065168 X0 X1
       have r₂ := eq12 (τ X1) (τ X0)
       grind)
    | exact resolve eq1065168 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065168
  have eq1065277 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1065185 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq1065185
    | (have j0 := eq1065185 X0 X1
       grind)
    | exact resolve eq1065185 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1065185
  have eq1065430 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ (τ (k (σ X0) X1))) = (τ (M.op (τ X1) X0)) ∨ (τ (k (σ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1065277 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1065277
    | exact resolve eq1065277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065277
  have eq1066140 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ (τ (k (σ X0) X1))) = (τ (M.op (τ X1) X0)) ∨ (τ (k (σ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1065430 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq1065430
    | (have j0 := eq1065430 X0 X1
       grind)
    | exact resolve eq1065430 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065430
  have eq1066248 : ∀ X0 X1 : G, (τ (k X0 (τ X1))) = (τ (M.op (τ X1) X0)) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ (k (σ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1066140 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq1066140
    | (have j0 := eq1066140 X0 X1
       grind)
    | exact resolve eq1066140 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066140
  have eq1066333 : ∀ X0 X1 : G, (τ (k X0 (τ X1))) = (τ (M.op (τ X1) X0)) ∨ (k X0 (τ X1)) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1066248 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq1066248
    | (have j0 := eq1066248 X0 X1
       grind)
    | exact resolve eq1066248 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066248
  have eq1067216 : ∀ X0 X1 : G, (k X1 (τ X0)) = (σ (τ (M.op (τ X0) X1))) ∨ (k X1 (τ X0)) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 (τ X0))
       have i₂ := eq1066333 X1 X0
       grind)
    | exact superpose eq1066333 eq11
    | (have j1 := eq1066333 X1 X0
       grind)
    | exact resolve eq11 eq1066333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066333
  have eq1069136 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1067216 X0 X1
       have i₂ := eq11 (M.op (τ X0) X1)
       grind)
    | exact superpose eq11 eq1067216
    | (have j0 := eq1067216 X0 X1
       grind)
    | exact resolve eq1067216 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067216
  have eq1069137 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1069136 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069136
  have eq1069203 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1069137 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1069137
    | exact resolve eq1069137 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1069393 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq1069137 X0 X1
       grind)
    | exact superpose eq1069137 eq18
    | (have j1 := eq1069137 X0 X1
       grind)
    | exact resolve eq18 eq1069137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1069137
  have eq1071850 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq1069203 (σ X0) X1
       grind)
    | exact superpose eq1069203 eq22
    | (have j1 := eq1069203 (σ X0) X1
       grind)
    | exact resolve eq22 eq1069203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1069203
  have eq1074265 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1069393 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1069393
    | exact resolve eq1069393 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069393
  have eq1074776 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1074265 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1074265
    | (have j0 := eq1074265 X0 X1
       grind)
    | exact resolve eq1074265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074265
  have eq1076496 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1071850 X1 (σ X0)
       grind)
    | exact superpose eq1071850 eq28
    | (have j1 := eq1071850 X1 (σ X0)
       grind)
    | exact resolve eq28 eq1071850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1071850
  have eq1077405 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1076496 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1076496
    | (have j0 := eq1076496 X0 X1
       grind)
    | exact resolve eq1076496 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076496
  have eq1077825 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1077405 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1077405
    | (have j0 := eq1077405 X0 X1
       grind)
    | exact resolve eq1077405 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077405
  have eq1077893 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1077825 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1077825
    | (have j0 := eq1077825 X0 X1
       grind)
    | exact resolve eq1077825 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077825
  have eq1080902 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq1077893 X0 X1
       grind)
    | exact superpose eq1077893 eq11
    | (have j1 := eq1077893 X0 X1
       grind)
    | exact resolve eq11 eq1077893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077893
  have eq1082631 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1080902 y x
       grind)
    | exact superpose eq1080902 eq16
    | (have j1 := eq1080902 y x
       grind)
    | exact resolve eq16 eq1080902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080902
  have eq1083219 : y = (k y x) := by
    first
    | (have j1 := eq1074776 x y
       grind)
    | (have r₁ := eq1082631
       have r₂ := eq1074776 x y
       grind)
    | exact resolve eq1082631 eq1074776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074776 eq1082631
  have eq1083517 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5047 x y
       have i₂ := eq1083219
       grind)
    | exact superpose eq1083219 eq5047
    | (have j0 := eq5047 y x
       grind)
    | exact resolve eq5047 eq1083219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5047
  have eq1083567 : y ≠ y ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq31599 y x
       have i₂ := eq1083219
       grind)
    | exact superpose eq1083219 eq31599
    | (have j0 := eq31599 y x
       grind)
    | (have r₁ := eq31599 y x
       have r₂ := eq1083219
       grind)
    | exact resolve eq31599 eq1083219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31599
  have eq1083603 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq1083567
  have eq1083605 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1083517
  have eq1083629 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1083603
       grind)
    | exact superpose eq1083603 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1083603
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1083603
       grind)
    | exact resolve eq13 eq1083603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083603
  have eq1083646 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq1083629
  have eq1083647 : y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq1083646
  have eq1083649 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1083647
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1083647 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083647
  have eq1083651 : y = (M.op x y) := by
    first
    | (have i₁ := eq1083649
       have i₂ := eq1083219
       grind)
    | exact superpose eq1083219 eq1083649
    | exact resolve eq1083649 eq1083219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083649
  have eq1200806 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq1083605
       grind)
    | exact superpose eq1083605 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1083605
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1083605
       grind)
    | exact resolve eq13 eq1083605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083605
  have eq1200824 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1200806
  have eq1200825 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1200824
  have eq1200842 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq1200825
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq1200825 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200825
  have eq1200876 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1200842
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1200842
    | exact resolve eq1200842 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200842
  have eq1200883 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1200876
       have i₂ := eq1083219
       grind)
    | exact superpose eq1083219 eq1200876
    | exact resolve eq1200876 eq1083219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083219 eq1200876
  have eq1200888 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1200883
       grind)
    | exact superpose eq1200883 eq16
    | exact resolve eq16 eq1200883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200883
  have eq1201073 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1200888
       have i₂ := eq1083651
       grind)
    | exact superpose eq1083651 eq1200888
    | exact resolve eq1200888 eq1083651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083651 eq1200888
  have eq1201074 : False := by grind
  exact eq1201074
