import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pyx_Equation2998 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq9 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq32 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq32
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq75 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq10
    | exact resolve eq10 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq127 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq26 (M.op X0 X0) x x X3
       have i₂ := eq25 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq25 eq26
    | exact resolve eq26 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq26
  have eq140 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq165 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq140 y x
       grind)
    | exact superpose eq140 eq16
    | (have j1 := eq140 y x
       grind)
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq190 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq127 (τ X0) X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq127
    | exact resolve eq127 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq222 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (τ (M.op X1 X1))) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (τ (M.op X1 X1)) X0
       have i₂ := eq190 X1 (M.op X0 (τ (M.op X1 X1)))
       grind)
    | exact superpose eq190 eq9
    | exact resolve eq9 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq792 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq165
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq165
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq165
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq165
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq165 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq793 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq792
  have eq799 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (τ (σ (M.op X0 X0)))) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq222 X1 (σ X0) X2
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq222
    | exact resolve eq222 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq861 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X0 X0)) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq799 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq799
    | exact resolve eq799 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq871 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (σ (M.op X0 X0))) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq861 (σ X0) X1 X2
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq861
    | exact resolve eq861 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq1734 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq871 X0 (σ (M.op X0 X0)) X1
       have i₂ := eq127 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       grind)
    | exact superpose eq127 eq871
    | exact resolve eq871 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq9409 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq793
       grind)
    | exact superpose eq793 eq16
    | exact resolve eq16 eq793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq9410 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq9409
       have r₂ := eq23 x
       grind)
    | exact resolve eq9409 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9409
  have eq330272 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op x X0) = X0 ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq127 y X0
       have i₂ := eq9410
       grind)
    | exact superpose eq9410 eq127
    | exact resolve eq127 eq9410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9410
  have eq2556189 : ∀ X0 : G, y = (τ (σ x)) ∨ (M.op x X0) = X0 ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq330272 X0
       grind)
    | exact superpose eq330272 eq10
    | (have j1 := eq330272 X0
       grind)
    | exact resolve eq10 eq330272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330272
  have eq2557101 : ∀ X0 : G, x = y ∨ (M.op x X0) = X0 ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq2556189 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2556189
    | (have j0 := eq2556189 X0
       grind)
    | exact resolve eq2556189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2556189
  have eq2557105 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x X0) = X0 ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq2557101 X0
       grind)
    | exact superpose eq2557101 eq16
    | (have j1 := eq2557101 X0
       grind)
    | exact resolve eq16 eq2557101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557101
  have eq2557113 : ∀ X0 : G, (σ x) = (σ (M.op y y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2557105 X0
       grind)
    | (have r₁ := eq2557105 X0
       have r₂ := eq23 x
       grind)
    | exact resolve eq2557105 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2557105
  have eq2557353 : ∀ X0 : G, (M.op y y) = (τ (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2557113 X0
       grind)
    | exact superpose eq2557113 eq10
    | (have j1 := eq2557113 X0
       grind)
    | exact resolve eq10 eq2557113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557113
  have eq2558546 : ∀ X0 : G, x = (M.op y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2557353 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2557353
    | (have j0 := eq2557353 X0
       grind)
    | exact resolve eq2557353 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557353
  have eq2558624 : ∀ X0 X1 : G, (M.op x X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq127 y X0
       have i₂ := eq2558546 X1
       grind)
    | exact superpose eq2558546 eq127
    | (have j1 := eq2558546 X0
       grind)
    | exact resolve eq127 eq2558546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq2558546
  have eq2560725 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2558624 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558624
  have eq2560726 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2560725 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560725
  have eq2561672 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1734 x X0
       have i₂ := eq2560726 x
       grind)
    | exact superpose eq2560726 eq1734
    | exact resolve eq1734 eq2560726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq2567137 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2561672 (σ y)
       grind)
    | exact superpose eq2561672 eq16
    | exact resolve eq16 eq2561672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561672
  have eq2569890 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2567137
       have i₂ := eq2560726 y
       grind)
    | exact superpose eq2560726 eq2567137
    | exact resolve eq2567137 eq2560726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560726 eq2567137
  have eq2569891 : False := by grind
  exact eq2569891

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxy_pxx_pxy_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq70
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70
    | exact resolve eq70 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq73
    | exact resolve eq73 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq272 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq283 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq272 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq272
    | exact resolve eq272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq284 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq283
  have eq410 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (σ (M.op X0 X0))) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq484 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 x (M.op X0 X0) X2
       have i₂ := eq54 x (M.op X0 X0) X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54
  have eq599 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq284 X0
       grind)
    | exact superpose eq284 eq16
    | exact resolve eq16 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq1123 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq484 X0 X1 x
       grind)
    | exact superpose eq484 eq14
    | exact resolve eq14 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq1685 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (σ (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq566 (M.op X0 (σ (M.op X1 X1))) X0 X2
       have i₂ := eq410 X1 X0 (M.op X0 (σ (M.op X1 X1)))
       grind)
    | exact superpose eq410 eq566
    | exact resolve eq566 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq566
  have eq8005 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1123 X1 (τ X0) X2
       have i₂ := eq599 X0
       grind)
    | exact superpose eq599 eq1123
    | exact resolve eq1123 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599 eq1123
  have eq61654 : ∀ X0 : G, y = (M.op (M.op y x) (M.op y (σ (M.op X0 X0)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1685 y X0 y
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq1685
    | exact resolve eq1685 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq61658 : x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq61654 x
       have i₂ := eq1685 y x x
       grind)
    | exact superpose eq1685 eq61654
    | exact resolve eq61654 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685 eq61654
  have eq61659 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq61658
  have eq61696 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq61659 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq61659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61659
  have eq61697 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq61696
    | exact resolve eq61696 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61696
  have eq61708 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq61697
       have r₂ := eq28
       grind)
    | exact resolve eq61697 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61697
  have eq61967 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (τ (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq61708 eq8005
    | exact resolve eq8005 eq61708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61708
  have eq61968 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq61967 x
       have i₂ := eq8005 x sF3 sF2
       grind)
    | exact superpose eq8005 eq61967
    | exact resolve eq61967 eq8005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8005 eq61967
  have eq61969 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq61968
  have eq61999 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq61969 eq30
    | exact resolve eq30 eq61969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq61969
  have eq62126 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq61999
    | exact resolve eq61999 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq61999
  have eq62127 : x = y := by grind
  clear eq62126
  have eq62502 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq62127
       grind)
    | exact superpose eq62127 eq19
    | exact resolve eq19 eq62127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq62503 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq62127
       grind)
    | exact superpose eq62127 eq25
    | exact resolve eq25 eq62127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq62127
  have eq62631 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq62503
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq62503
    | exact resolve eq62503 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq62503
  have eq62663 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq62631 eq27
    | exact resolve eq27 eq62631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq62631
  have eq63947 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq62663 eq66
    | exact resolve eq66 eq62663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq62663
  have eq64266 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq63947
       have i₂ := eq62502
       grind)
    | exact superpose eq62502 eq63947
    | exact resolve eq63947 eq62502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62502 eq63947
  have eq64281 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64266 eq15
    | exact resolve eq15 eq64266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64266
  have eq64362 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq64281
    | exact resolve eq64281 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq64281
  have eq64385 : False := by grind
  exact eq64385

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pxy_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq16 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (k X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1 X2
       have i₂ := eq174 X2
       grind)
    | exact superpose eq174 eq176
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq179 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (M.op X1 (k X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq181 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (k X0 X0)) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X2) (k X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (k X1 X1) (k X0 X0)
       have i₂ := eq179 X1 (k X0 X0) X0
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X2 X3 : G, (M.op X0 (k X2 X2)) = (M.op X0 (k X3 X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq543 x X2 (M.op X0 (k X3 X3))
       have i₂ := eq179 x X0 X3
       grind)
    | exact superpose eq179 eq543
    | exact resolve eq543 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op (k X1 X1) X0)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq181 x (M.op (k X1 X1) X0) X3
       have i₂ := eq543 X1 x X0
       grind)
    | exact superpose eq543 eq181
    | exact resolve eq181 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq569 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X0) = (M.op (k X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X1 (M.op (k X2 X2) X0) x
       have i₂ := eq543 X2 x X0
       grind)
    | exact superpose eq543 eq179
    | exact resolve eq179 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq606 : ∀ X0 X1 X2 X3 : G, (k X2 X2) = (M.op (M.op (k X0 X0) (k X1 X1)) (k X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq543 X0 X3 (k X2 X2)
       have i₂ := eq562 (k X0 X0) X2 X1
       grind)
    | (have i₁ := eq543 X0 X3 (k X2 X2)
       have i₂ := eq562 (k X0 X0) X1 X2
       grind)
    | exact superpose eq562 eq543
    | exact resolve eq543 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq607 : ∀ X1 X2 : G, (k X2 X2) = (k X1 X1) := by
    intro X1 X2
    first
    | (have i₁ := eq606 x X1 X2 x
       have i₂ := eq543 x x (k X1 X1)
       grind)
    | exact superpose eq543 eq606
    | exact resolve eq606 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq606
  have eq668 : ∀ X0 X1 : G, (k X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq607 X0 (σ X1)
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq607 (σ X1) X0
       grind)
    | exact superpose eq607 eq10
    | exact resolve eq10 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : ∀ X0 : G, (k y y) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq115
       have i₂ := eq607 x sF3
       grind)
    | (have i₁ := eq115
       have i₂ := eq607 sF3 x
       grind)
    | exact superpose eq607 eq115
    | exact resolve eq115 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq728 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq668 X1 x
       have i₂ := eq668 x X0
       grind)
    | exact superpose eq668 eq668
    | exact resolve eq668 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1068 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (σ (σ (k X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq728 x X1
       have i₂ := eq728 X0 x
       grind)
    | exact superpose eq728 eq728
    | exact resolve eq728 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1093 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq668 X1 x
       have i₂ := eq728 X0 x
       grind)
    | exact superpose eq728 eq668
    | exact resolve eq668 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq1579 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op (k X1 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq568
    | exact resolve eq568 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1588 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (k X0 X0) x)) := by
    intro X0
    first
    | (have i₁ := eq568 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq568
    | (have j0 := eq568 x X0 y
       grind)
    | exact resolve eq568 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1589 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (k X0 X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq568
    | (have j0 := eq568 (σ x) X0 (σ y)
       grind)
    | exact resolve eq568 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1654 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ x = y := by
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
  have eq1655 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq1657 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1655
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq1655
    | exact resolve eq1655 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655
  have eq1658 : (M.op x y) = (k x y) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1654
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1654
    | exact resolve eq1654 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654
  have eq1907 : ∀ X0 X1 X2 : G, (M.op (k X2 X2) (M.op (k X1 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq569 (M.op (k X1 X1) X0) X0 X2
       have i₂ := eq1579 X0 X1
       grind)
    | exact superpose eq1579 eq569
    | exact resolve eq569 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq1579
  have eq3642 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1658
       grind)
    | exact superpose eq1658 eq40
    | exact resolve eq40 eq1658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1658
  have eq3643 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq3642
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3642
    | exact resolve eq3642 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3642
  have eq3645 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq20 eq3643
    | exact resolve eq3643 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3643
  have eq6764 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq3645 eq1657
    | exact resolve eq1657 eq3645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1657 eq3645
  have eq6771 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | (have r₁ := eq6764
       have r₂ := eq27
       grind)
    | exact resolve eq6764 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6764
  have eq6821 : (τ (σ y)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq6771 eq679
    | exact resolve eq679 eq6771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679 eq6771
  have eq6893 : y = (k y y) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq31 eq6821
    | exact resolve eq6821 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6821
  have eq6894 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6893
  have eq6982 : ∀ X0 : G, y = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq607 y X0
       have i₂ := eq6894
       grind)
    | exact superpose eq6894 eq607
    | exact resolve eq607 eq6894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq6983 : ∀ X0 : G, (σ y) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq668 X0 y
       have i₂ := eq6894
       grind)
    | exact superpose eq6894 eq668
    | exact resolve eq668 eq6894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq6993 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1068 y X0
       have i₂ := eq6894
       grind)
    | exact superpose eq6894 eq1068
    | exact resolve eq1068 eq6894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq6994 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1093 y X0
       have i₂ := eq6894
       grind)
    | exact superpose eq6894 eq1093
    | exact resolve eq1093 eq6894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq7013 : y = (M.op (M.op x y) (M.op y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1588 y
       have i₂ := eq6894
       grind)
    | exact superpose eq6894 eq1588
    | exact resolve eq1588 eq6894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588
  have eq7014 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1589 y
       have i₂ := eq6894
       grind)
    | exact superpose eq6894 eq1589
    | exact resolve eq1589 eq6894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589 eq6894
  have eq7069 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq6994 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6994
    | (have j0 := eq6994 X0
       grind)
    | exact resolve eq6994 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6994
  have eq7070 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq6993 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6993
    | (have j0 := eq6993 X0
       grind)
    | exact resolve eq6993 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6993
  have eq7079 : ∀ X0 : G, (σ y) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq6983 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6983
    | (have j0 := eq6983 X0
       grind)
    | exact resolve eq6983 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6983
  have eq7126 : y = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6982 eq7069
    | exact resolve eq7069 eq6982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7069
  have eq7127 : y = (σ (σ (σ (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6982 eq7070
    | exact resolve eq7070 eq6982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7070
  have eq7160 : y = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7126 eq7127
    | exact resolve eq7127 eq7126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7126 eq7127
  have eq7165 : (σ x) = (σ y) ∨ y = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq7160
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7160
    | exact resolve eq7160 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7160
  have eq7168 : y = (τ (σ x)) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq7165 eq31
    | exact resolve eq31 eq7165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7190 : x = y ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq7168
    | exact resolve eq7168 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7168
  have eq7191 : y = (σ y) ∨ x = y := by grind
  clear eq7190
  have eq7195 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (σ y) X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq7191
       grind)
    | exact superpose eq7191 eq36
    | exact resolve eq36 eq7191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq7210 : x ≠ (σ y) ∨ x = y := by grind
  clear eq7191
  have eq7436 : ∀ X1 X2 : G, (M.op y (M.op (k X1 X1) X2)) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1 X2
    first
    | (have i₁ := eq1907 X2 X1 x
       have i₂ := eq6982 x
       grind)
    | exact superpose eq6982 eq1907
    | exact resolve eq1907 eq6982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907
  have eq7528 : ∀ X2 : G, (M.op y (M.op y X2)) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X2
    first
    | exact superpose eq6982 eq7436
    | exact resolve eq7436 eq6982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7436
  have eq7630 : ∀ X2 : G, (M.op (σ y) (M.op (σ y) X2)) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X2
    first
    | exact superpose eq7165 eq7528
    | exact resolve eq7528 eq7165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7528
  have eq8452 : ∀ X0 : G, (M.op y x) = (M.op y (M.op (k X0 X0) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq7013 eq568
    | exact resolve eq568 eq7013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7013
  have eq8454 : (M.op y x) = (M.op y (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6982 eq8452
    | exact resolve eq8452 eq6982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8452
  have eq8461 : (M.op (σ y) x) = (M.op (σ y) (M.op (σ y) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7165 eq8454
    | exact resolve eq8454 eq7165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8454
  have eq8468 : (M.op x y) = (M.op (σ y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7630 eq8461
    | exact resolve eq8461 eq7630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8461
  have eq8484 : (M.op x y) = (k (σ y) x) ∨ x = (M.op x x) ∨ x = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8468 eq11
    | (have j0 := eq11 (M.op x x) x
       grind)
    | exact resolve eq11 eq8468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8468
  have eq8487 : (M.op x y) = (k (σ y) x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq8484
       have r₂ := eq7210
       grind)
    | exact resolve eq8484 eq7210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8484
  have eq8492 : x = (k x x) ∨ (M.op x y) = (k (σ y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8487
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq8487
    | exact resolve eq8487 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8487
  have eq8497 : x = (σ y) ∨ (M.op x y) = (k (σ y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7079 eq8492
    | exact resolve eq8492 eq7079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7079 eq8492
  have eq8502 : (M.op x y) = (k (σ y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq8497
       have r₂ := eq7210
       grind)
    | exact resolve eq8497 eq7210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7210 eq8497
  have eq8512 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8502 eq7195
    | exact resolve eq7195 eq8502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7195 eq8502
  have eq8515 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq8512
  have eq8518 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8515
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8515
    | exact resolve eq8515 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8515
  have eq8520 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq8518
    | exact resolve eq8518 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8518
  have eq8565 : ∀ X0 : G, (M.op y (σ x)) = (M.op (σ y) (M.op (k X0 X0) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq7014 eq568
    | exact resolve eq568 eq7014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq7014
  have eq8566 : (M.op y (σ x)) = (M.op (σ y) (M.op y (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6982 eq8565
    | exact resolve eq8565 eq6982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8565
  have eq8572 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7165 eq8566
    | exact resolve eq8566 eq7165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8566
  have eq8579 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7630 eq8572
    | exact resolve eq8572 eq7630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7630 eq8572
  have eq8599 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8579 eq11
    | (have j0 := eq11 (M.op (σ x) (σ x)) (σ x)
       grind)
    | exact resolve eq11 eq8579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8579
  have eq8601 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8599
  have eq8604 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8601
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq8601
    | exact resolve eq8601 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8601
  have eq8609 : y = (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6982 eq8604
    | exact resolve eq8604 eq6982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6982 eq8604
  have eq8614 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7165 eq8609
    | exact resolve eq8609 eq7165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7165 eq8609
  have eq8615 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq8614
  have eq8621 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq8520 eq8615
    | exact resolve eq8615 eq8520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8520 eq8615
  have eq8626 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq8621
       have r₂ := eq27
       grind)
    | exact resolve eq8621 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8621
  have eq8631 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq8626 eq31
    | exact resolve eq31 eq8626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq8626
  have eq8661 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq8631
    | exact resolve eq8631 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq8631
  have eq8662 : x = y := by grind
  clear eq8661
  have eq8674 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8662
       grind)
    | exact superpose eq8662 eq18
    | exact resolve eq18 eq8662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq8675 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8662
       grind)
    | exact superpose eq8662 eq24
    | exact resolve eq24 eq8662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8662
  have eq8692 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq8675
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8675
    | exact resolve eq8675 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8675
  have eq8693 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq8674
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq8674
    | exact resolve eq8674 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8674
  have eq8975 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8692 eq26
    | exact resolve eq26 eq8692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8692
  have eq9001 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq8975
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq8975
    | exact resolve eq8975 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq8975
  have eq9007 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq8693
       grind)
    | exact superpose eq8693 eq39
    | exact resolve eq39 eq8693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq8693
  have eq9173 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9007
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9007
    | exact resolve eq9007 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9007
  have eq9215 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9001 eq9173
    | exact resolve eq9173 eq9001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9001 eq9173
  have eq9231 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9215
    | exact resolve eq9215 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9215
  have eq9233 : False := by grind
  exact eq9233

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyy_x_pyx_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
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
  have eq44 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq44
    | (have j0 := eq44 (σ X0) (σ X1)
       grind)
    | exact resolve eq44 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X1) ∨ (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    grind
  have eq88 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
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
  have eq89 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq97 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq89
    | exact resolve eq89 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq89
  have eq101 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq97 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq146 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57 y x
       grind)
    | exact superpose eq57 eq16
    | (have j1 := eq57 y x
       grind)
    | exact resolve eq16 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq174 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0) (σ X0)
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq26
    | exact resolve eq26 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq79 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq262 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq259 X0
       have i₂ := eq26 X0 X0
       grind)
    | exact superpose eq26 eq259
    | (have j0 := eq259 X0
       grind)
    | exact resolve eq259 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq263 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq262 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq760 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq146
       have i₂ := eq101 x
       grind)
    | exact superpose eq101 eq146
    | exact resolve eq146 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq146
  have eq790 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq760
       have i₂ := eq44 y x
       grind)
    | exact superpose eq44 eq760
    | (have j1 := eq44 y x
       grind)
    | exact resolve eq760 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq793 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq790
  have eq824 : y = (k y x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq263 x
       have i₂ := eq793
       grind)
    | exact superpose eq793 eq263
    | exact resolve eq263 eq793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq830 : y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq26 x x
       have i₂ := eq793
       grind)
    | exact superpose eq793 eq26
    | exact resolve eq26 eq793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq837 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq760
       have i₂ := eq824
       grind)
    | exact superpose eq824 eq760
    | exact resolve eq760 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq824
  have eq840 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq837
  have eq1083 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq840
       have i₂ := eq830
       grind)
    | exact superpose eq830 eq840
    | exact resolve eq840 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq840
  have eq1084 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1083
  have eq1085 : (σ y) = (σ (M.op x x)) := by grind
  clear eq1084
  have eq1180 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq174 x
       have i₂ := eq1085
       grind)
    | exact superpose eq1085 eq174
    | exact resolve eq174 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq1181 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1085
       grind)
    | exact superpose eq1085 eq10
    | exact resolve eq10 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1218 : y = (M.op x x) := by
    first
    | (have i₁ := eq1181
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1181
    | exact resolve eq1181 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181
  have eq1236 : y = (M.op x y) := by
    first
    | (have i₁ := eq26 x x
       have i₂ := eq1218
       grind)
    | exact superpose eq1218 eq26
    | exact resolve eq26 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1218
  have eq1383 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1180
       grind)
    | exact superpose eq1180 eq16
    | exact resolve eq16 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq1397 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1383
       have i₂ := eq1236
       grind)
    | exact superpose eq1236 eq1383
    | exact resolve eq1383 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236 eq1383
  have eq1398 : False := by grind
  exact eq1398

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_pxx_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq70 (σ X0)
       grind)
    | exact superpose eq70 eq15
    | exact resolve eq15 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq73
    | exact resolve eq73 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq73
  have eq582 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq582 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq692 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq591 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq696 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq692 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq692 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq692 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq692 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq692 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq748 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq696 X1 (τ X0)
       grind)
    | exact superpose eq696 eq19
    | (have j1 := eq696 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq751 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq696 (σ X1) (σ X0)
       grind)
    | exact superpose eq696 eq15
    | (have j1 := eq696 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq832 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq748 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq748
    | exact resolve eq748 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq877 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq832 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq832
    | (have j0 := eq832 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq832 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq1047 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq751 x y
       grind)
    | exact superpose eq751 eq16
    | (have j1 := eq751 x y
       grind)
    | exact resolve eq16 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq1076 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1047
       have i₂ := eq877 x y
       grind)
    | exact superpose eq877 eq1047
    | (have j1 := eq877 (σ x) (σ y)
       grind)
    | (have r₁ := eq1047
       have r₂ := eq877 x y
       grind)
    | (have r₁ := eq1047
       have r₂ := eq877 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1047
       have r₂ := eq877 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1047 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq1047
  have eq1077 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1076
  have eq1081 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1077
       grind)
    | exact superpose eq1077 eq10
    | exact resolve eq10 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1123 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1081
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1081
    | exact resolve eq1081 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1124 : x = y := by grind
  clear eq1123
  have eq1126 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1124
       grind)
    | exact superpose eq1124 eq16
    | exact resolve eq16 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1127 : False := by grind
  exact eq1127

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_y_pxy_y_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
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
  clear eq24
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X1) X2) X2)) ≠ X0 ∨ (k (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op (M.op X0 X1) X2) X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k y x) := by
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
  have eq78 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq100
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq16
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq805 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 X1) X0 X0
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq64
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq8280 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8281 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq8280
    | exact resolve eq8280 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8280
  have eq8292 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq8281
       have r₂ := eq27
       grind)
    | exact resolve eq8281 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8281
  have eq8296 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq8292
    | exact resolve eq8292 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8292
  have eq8298 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq8296
    | exact resolve eq8296 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8296
  have eq8301 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq8298 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8298
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8298
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq8298
       grind)
    | exact resolve eq13 eq8298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8298
  have eq8324 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq8301
       have r₂ := eq26
       grind)
    | exact resolve eq8301 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8301
  have eq8502 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq8324 eq118
    | exact resolve eq118 eq8324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8324
  have eq8510 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8502
  have eq8512 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8510
       have r₂ := eq27
       grind)
    | exact resolve eq8510 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8510
  have eq8515 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq8512
       grind)
    | exact superpose eq8512 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq8512
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8512
       grind)
    | exact resolve eq13 eq8512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8538 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8515
       have r₂ := eq18
       grind)
    | exact resolve eq8515 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8515
  have eq8562 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq8538
       grind)
    | exact superpose eq8538 eq100
    | exact resolve eq100 eq8538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8538
  have eq8576 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8562
    | exact resolve eq8562 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8562
  have eq8739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8576 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq8576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8742 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8739
    | exact resolve eq8739 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8739
  have eq8753 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8742
       have r₂ := eq27
       grind)
    | exact resolve eq8742 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8742
  have eq8757 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8753
    | exact resolve eq8753 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8753
  have eq8758 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8757
  have eq8761 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8758
    | exact resolve eq8758 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8758
  have eq8948 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8761 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8761
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8761
       grind)
    | exact resolve eq13 eq8761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8761
  have eq8972 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8948
       have r₂ := eq26
       grind)
    | exact resolve eq8948 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8948
  have eq9009 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8972 eq8576
    | exact resolve eq8576 eq8972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8576 eq8972
  have eq9011 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9009
  have eq9015 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9011
       have r₂ := eq27
       grind)
    | exact resolve eq9011 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9011
  have eq9017 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9015 eq27
    | exact resolve eq27 eq9015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9019 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9015 eq78
    | (have r₁ := eq78
       have r₂ := eq9015
       grind)
    | exact resolve eq78 eq9015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq9036 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq9019
  have eq16113 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9036 eq118
    | exact resolve eq118 eq9036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16128 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq16113
  have eq16142 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16128
       have r₂ := eq9017
       grind)
    | exact resolve eq16128 eq9017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16128
  have eq16220 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16142 eq805
    | exact resolve eq805 eq16142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16142
  have eq16227 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16220
    | exact resolve eq16220 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16220
  have eq16234 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16227
       have r₂ := eq8512
       grind)
    | exact resolve eq16227 eq8512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8512 eq16227
  have eq16637 : (τ (σ x)) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16234 eq114
    | exact resolve eq114 eq16234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq16638 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16234 eq118
    | exact resolve eq118 eq16234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq16234
  have eq16653 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq16638
  have eq16667 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16653
       have r₂ := eq9017
       grind)
    | exact resolve eq16653 eq9017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16653
  have eq16668 : x = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq16637
    | exact resolve eq16637 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq16637
  have eq16675 : x = (k y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq16668
       have r₂ := eq77
       grind)
    | exact resolve eq16668 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq16668
  have eq16677 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq16667
       grind)
    | exact superpose eq16667 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq16667
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16667
       grind)
    | exact resolve eq13 eq16667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16667
  have eq16722 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16677
       have r₂ := eq18
       grind)
    | exact resolve eq16677 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16677
  have eq16768 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq16722
       grind)
    | exact superpose eq16722 eq100
    | exact resolve eq100 eq16722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16722
  have eq16782 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq16768
    | exact resolve eq16768 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16768
  have eq17124 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16782 eq9036
    | exact resolve eq9036 eq16782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9036
  have eq17128 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq17124
  have eq17136 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17128
       have r₂ := eq9017
       grind)
    | exact resolve eq17128 eq9017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17128
  have eq17226 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17136 eq805
    | exact resolve eq805 eq17136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17136
  have eq17233 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17226
    | exact resolve eq17226 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17226
  have eq17240 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17233
       have r₂ := eq9015
       grind)
    | exact resolve eq17233 eq9015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9015 eq17233
  have eq17573 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17240 eq16782
    | exact resolve eq16782 eq17240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16782 eq17240
  have eq17576 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq17573
  have eq17588 : x = (M.op x y) := by
    first
    | (have r₁ := eq17576
       have r₂ := eq9017
       grind)
    | exact resolve eq17576 eq9017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9017 eq17576
  have eq17606 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq17588 eq20
    | exact resolve eq20 eq17588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq17736 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq17606
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17606
    | exact resolve eq17606 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17606
  have eq17958 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq17736 eq26
    | exact resolve eq26 eq17736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq21906 : x = (k y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq17588 eq16675
    | exact resolve eq16675 eq17588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16675
  have eq21910 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq21906
       grind)
    | exact superpose eq21906 eq100
    | exact resolve eq100 eq21906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21906
  have eq21933 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq17736 eq21910
    | exact resolve eq21910 eq17736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21910
  have eq21941 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq21933
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21933
    | exact resolve eq21933 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21933
  have eq21948 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq17736 eq21941
    | exact resolve eq21941 eq17736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21941
  have eq21964 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21948 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq21948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21965 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by grind
  clear eq21964
  have eq21967 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq17958 eq21965
    | exact resolve eq21965 eq17958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21965
  have eq21976 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq21967
       have r₂ := eq27
       grind)
    | exact resolve eq21967 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21967
  have eq21985 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq17958 eq21976
    | exact resolve eq21976 eq17958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21976
  have eq22001 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21985 eq13
    | exact resolve eq13 eq21985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21985
  have eq22054 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq22001
       have r₂ := eq17958
       grind)
    | exact resolve eq22001 eq17958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22001
  have eq22117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22054 eq21948
    | exact resolve eq21948 eq22054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21948 eq22054
  have eq22119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq22117
  have eq22121 : x = (M.op y x) := by
    first
    | (have r₁ := eq22119
       have r₂ := eq27
       grind)
    | exact resolve eq22119 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22119
  have eq22185 : x ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq805 y x
       have i₂ := eq22121
       grind)
    | exact superpose eq22121 eq805
    | exact resolve eq805 eq22121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805 eq22121
  have eq22194 : x ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq22185
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22185
    | exact resolve eq22185 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq22185
  have eq22211 : x = (k y x) := by
    first
    | (have r₁ := eq22194
       have r₂ := eq17588
       grind)
    | exact resolve eq22194 eq17588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17588 eq22194
  have eq22840 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq22211
       grind)
    | exact superpose eq22211 eq100
    | exact resolve eq100 eq22211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq22211
  have eq22863 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq17736 eq22840
    | exact resolve eq22840 eq17736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22840
  have eq22871 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq22863
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22863
    | exact resolve eq22863 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq22863
  have eq22878 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq17736 eq22871
    | exact resolve eq22871 eq17736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17736 eq22871
  have eq23491 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq22878 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq22878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23492 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq23491
  have eq23494 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq17958 eq23492
    | exact resolve eq23492 eq17958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23492
  have eq23503 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq23494
       have r₂ := eq27
       grind)
    | exact resolve eq23494 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23494
  have eq23512 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq17958 eq23503
    | exact resolve eq23503 eq17958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23503
  have eq23562 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq23512 eq13
    | exact resolve eq13 eq23512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23512
  have eq23617 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq23562
       have r₂ := eq17958
       grind)
    | exact resolve eq23562 eq17958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17958 eq23562
  have eq23619 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22878 eq23617
    | exact resolve eq23617 eq22878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22878 eq23617
  have eq23621 : False := by grind
  exact eq23621

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_pxx_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq38 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  clear eq33 eq35
  have eq53 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq246 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq53 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq12
    | (have j1 := eq53 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq265 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq246 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq271 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq265 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq265
    | (have j0 := eq265 X0 X1
       grind)
    | exact resolve eq265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq272 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq271 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq552 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq272
    | exact resolve eq272 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq272 x y
       grind)
    | exact superpose eq272 eq16
    | (have j1 := eq272 x y
       grind)
    | exact resolve eq16 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq580 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq552
    | (have j0 := eq552 X0 X1
       grind)
    | exact resolve eq552 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq552
  have eq585 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq580 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq580
    | exact resolve eq580 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq706 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq559
       have i₂ := eq585 x y
       grind)
    | exact superpose eq585 eq559
    | (have j1 := eq585 (σ x) (σ y)
       grind)
    | (have r₁ := eq559
       have r₂ := eq585 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq559
       have r₂ := eq585 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq559 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq585
  have eq709 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq706
  have eq731 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq709
       grind)
    | exact superpose eq709 eq10
    | exact resolve eq10 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq766 : x = y ∨ x = y := by
    first
    | (have i₁ := eq731
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq731
    | exact resolve eq731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq767 : x = y := by grind
  clear eq766
  have eq769 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq767
       grind)
    | exact superpose eq767 eq16
    | exact resolve eq16 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq770 : False := by grind
  exact eq770

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_x_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq38 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  clear eq33 eq35
  have eq53 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq246 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq53 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq12
    | (have j1 := eq53 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq265 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq246 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq271 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq265 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq265
    | (have j0 := eq265 X0 X1
       grind)
    | exact resolve eq265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq272 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq271 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq552 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq272
    | exact resolve eq272 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq272 x y
       grind)
    | exact superpose eq272 eq16
    | (have j1 := eq272 x y
       grind)
    | exact resolve eq16 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq580 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq552
    | (have j0 := eq552 X0 X1
       grind)
    | exact resolve eq552 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq552
  have eq585 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq580 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq580
    | exact resolve eq580 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq706 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq559
       have i₂ := eq585 x y
       grind)
    | exact superpose eq585 eq559
    | (have j1 := eq585 (σ x) (σ y)
       grind)
    | (have r₁ := eq559
       have r₂ := eq585 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq559
       have r₂ := eq585 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq559 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq585
  have eq709 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq706
  have eq731 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq709
       grind)
    | exact superpose eq709 eq10
    | exact resolve eq10 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq766 : x = y ∨ x = y := by
    first
    | (have i₁ := eq731
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq731
    | exact resolve eq731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq767 : x = y := by grind
  clear eq766
  have eq769 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq767
       grind)
    | exact superpose eq767 eq16
    | exact resolve eq16 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq770 : False := by grind
  exact eq770
