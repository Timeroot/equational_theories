import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2656`: `x = ((x ◇ x) ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_pyy_x_pyy_pyx_Equation2656 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2656 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2656.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  clear eq36
  have eq47 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op x y)) x) = X0 := by
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
  have eq48 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) (M.op X2 X3)) X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X0 X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq74 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op y y) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq81
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq16
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86
    | exact resolve eq86 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq106 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq124 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq106 eq16
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq195 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq47 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq47 eq14
    | exact resolve eq14 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) x) := by
    first
    | exact superpose eq195 eq47
    | exact resolve eq47 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq76 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq76
    | (have j0 := eq76 (σ X0)
       grind)
    | exact resolve eq76 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq44
    | (have j1 := eq76 x
       grind)
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq76
  have eq378 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq50 X0 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op X0 X1)
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq48
    | exact resolve eq48 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X2 X3)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X1) X2 X3
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq12
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq50 X0 X1
       grind)
    | exact resolve eq12 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq384 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq391 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq195 eq378
    | exact resolve eq378 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 (M.op X1 X1) X1 X2 x
       have i₂ := eq50 X1 X1
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X2 X2) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X2 X1 (M.op (M.op X0 X0) (M.op x x)) x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (k (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    have f450_10 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op X2 X3))) = X1 := by
      intro X0 X1 X2 X3
      grind
    have f450_15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
      intro X0 X1
      grind
    have f450_16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X0 := by
      intro X0 X1 X2
      grind
    have f450_18 : (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) ≠ (k (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) (M.op X0 X1)) := by grind
    have f450_21 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
      intro X0 X1
      first
      | (have i₁ := f450_16 (M.op (M.op X0 X1) (M.op X0 X1)) X0 X1
         have i₂ := f450_16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
         grind)
      | exact superpose f450_16 f450_16
      | exact resolve f450_16 f450_16
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f450_32 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (k (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) (M.op X0 X1)) := by
      intro X0 X1
      grind
    have f450_34 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) = (k (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) (M.op X0 X1)) := by
      intro X0 X1
      first
      | (have i₁ := f450_32 X0 X1
         have i₂ := f450_21 X0 X1
         grind)
      | exact superpose f450_21 f450_32
      | exact resolve f450_32 f450_21
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f450_151 : (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) ≠ (k (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) (M.op X0 X1)) := by
      first
      | (have i₁ := f450_18
         have i₂ := f450_21 X0 X1
         grind)
      | exact superpose f450_21 f450_18
      | exact resolve f450_18 f450_21
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f450_167 : False := by
      first
      | (have r₁ := f450_151
         have r₂ := f450_34 X0 X1
         grind)
      | exact resolve f450_151 f450_34
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f450_167
  have eq451 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))
       have i₂ := eq49 (M.op X0 X1) (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq49 eq47
    | exact resolve eq47 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq460 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 X1
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq451
    | exact resolve eq451 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq461 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) = (k (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 X1
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq450
    | exact resolve eq450 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq710 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq63 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq63 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq63 X0 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq726 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq710 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq727 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq726 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq729 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq727 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq727
    | (have j0 := eq727 X0 X1
       grind)
    | exact resolve eq727 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq1087 : (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | exact superpose eq196 eq47
    | exact resolve eq47 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq1109 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq195 eq1087
    | exact resolve eq1087 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1478 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) x) (M.op x y)) := by
    first
    | exact superpose eq1109 eq391
    | exact resolve eq391 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq1479 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) x) x) := by
    first
    | exact superpose eq1109 eq197
    | exact resolve eq197 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq1109
  have eq1667 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op (M.op X0 X0) X0)
       have i₂ := eq429 X0 X0 X0
       grind)
    | exact superpose eq429 eq47
    | exact resolve eq47 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1668 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq48 (M.op (M.op X0 X0) X0)
       have i₂ := eq429 X0 X0 X0
       grind)
    | exact superpose eq429 eq48
    | exact resolve eq48 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1898 : (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x x) x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq1667 eq379
    | exact resolve eq379 eq1667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1908 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq379 eq1898
    | exact resolve eq1898 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898
  have eq2104 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq1668 eq379
    | exact resolve eq379 eq1668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668
  have eq2114 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq379 eq2104
    | exact resolve eq2104 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq2104
  have eq4014 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X0) = (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq382 (M.op (M.op X0 X1) X2) (M.op X0 X1) X0 X1
       have i₂ := eq382 (M.op X0 X1) X2 (M.op X0 X1) X2
       grind)
    | exact superpose eq382 eq382
    | exact resolve eq382 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4246 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) ≠ X0 ∨ (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2))) ∨ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (k (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) (M.op (M.op X0 X0) X0)
       have i₂ := eq423 X0 X1 X2
       grind)
    | exact superpose eq423 eq12
    | (have j0 := eq12 (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq4263 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2))) ∨ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (k (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4246 X0 X1 X2
       grind)
    | (have r₁ := eq4246 X0 X1 X2
       have r₂ := eq429 X0 X0 X0
       grind)
    | exact resolve eq4246 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4246
  have eq4274 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) (M.op (M.op X0 X0) X0)) ∨ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (k (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4263 X0 X1 X2
       have i₂ := eq50 (M.op (M.op X0 X0) X0) (M.op X1 X2)
       grind)
    | exact superpose eq50 eq4263
    | (have j0 := eq4263 X0 X1 X2
       grind)
    | exact resolve eq4263 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4263
  have eq4279 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) (M.op (M.op X0 X0) X0)) = X0 ∨ (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4274 X0 X1 X2
       have i₂ := eq429 X0 X0 X0
       grind)
    | exact superpose eq429 eq4274
    | (have j0 := eq4274 X0 X1 X2
       grind)
    | exact resolve eq4274 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq4274
  have eq4872 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq350 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq6305 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op x y)) x) = (k (M.op (M.op (M.op X0 X1) (M.op x y)) x) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq461 X0 X1
       have i₂ := eq460 X0 X1
       grind)
    | exact superpose eq460 eq461
    | exact resolve eq461 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460 eq461
  have eq6387 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) x) = (k (M.op (M.op X0 X1) x) (M.op (M.op (M.op X0 X1) X0) (M.op (M.op x y) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6305 (M.op (M.op X0 X1) X0) (M.op sF0 x)
       have i₂ := eq382 X0 X1 sF0 x
       grind)
    | exact superpose eq382 eq6305
    | exact resolve eq6305 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq6305
  have eq10614 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq729 X0 X1
       have j1 := eq724 X0 X1
       grind)
    | (have r₁ := eq729 X0 X1
       have r₂ := eq724 X0 X1
       grind)
    | (have r₁ := eq729 (k X1 X0) X0
       have r₂ := eq724 X0 X1
       grind)
    | (have r₁ := eq729 X1 X1
       have r₂ := eq724 X1 X1
       grind)
    | exact resolve eq729 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq729
  have eq10885 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10614 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10614
    | (have j0 := eq10614 X0 y
       grind)
    | exact resolve eq10614 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10614
  have eq28669 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq94 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28670 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq28669
    | exact resolve eq28669 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28669
  have eq28681 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq28670
       have r₂ := eq28
       grind)
    | exact resolve eq28670 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28670
  have eq28683 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq28681
    | exact resolve eq28681 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28681
  have eq28685 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28683 eq75
    | (have r₁ := eq75
       have r₂ := eq28683
       grind)
    | exact resolve eq75 eq28683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28683
  have eq28776 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq28685
  have eq28777 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq28776
  have eq28826 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28777 eq94
    | exact resolve eq94 eq28777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28777
  have eq28835 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq28826
  have eq28838 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq28835
       have r₂ := eq28
       grind)
    | exact resolve eq28835 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28835
  have eq28843 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq28838
  have eq28974 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28843 eq94
    | exact resolve eq94 eq28843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq28843
  have eq28984 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq28974
  have eq28996 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq28984
       grind)
    | exact superpose eq28984 eq74
    | (have r₁ := eq74
       have r₂ := eq28984
       grind)
    | exact resolve eq74 eq28984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq28984
  have eq29086 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq28996
  have eq29087 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq29086
  have eq29152 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq29087
       grind)
    | exact superpose eq29087 eq81
    | exact resolve eq81 eq29087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29087
  have eq29172 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq29152
    | exact resolve eq29152 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29152
  have eq29207 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29172 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq29172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29212 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq29207
    | exact resolve eq29207 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29207
  have eq29223 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq29212
       have r₂ := eq28
       grind)
    | exact resolve eq29212 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29212
  have eq29225 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq29223
    | exact resolve eq29223 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29223
  have eq38705 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq10885 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10885
    | (have j0 := eq10885 x
       grind)
    | exact resolve eq10885 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10885
  have eq38763 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq38705
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq38705
    | exact resolve eq38705 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38705
  have eq38780 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq38763
    | exact resolve eq38763 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38763
  have eq40651 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29225 eq75
    | (have r₁ := eq75
       have r₂ := eq29225
       grind)
    | exact resolve eq75 eq29225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq29225
  have eq40760 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq40651
  have eq40761 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq40760
  have eq41665 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq40761 eq29172
    | exact resolve eq29172 eq40761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40761
  have eq41674 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq41665
  have eq41692 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq41674
       have r₂ := eq28
       grind)
    | exact resolve eq41674 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41674
  have eq42336 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq41692
  have eq42527 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq42336 eq29172
    | exact resolve eq29172 eq42336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29172 eq42336
  have eq42535 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq42527
  have eq42566 : y = (k y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  have eq42577 : y = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq378 y
       have i₂ := eq42535
       grind)
    | exact superpose eq42535 eq378
    | exact resolve eq378 eq42535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42620 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq50 y y
       have i₂ := eq42535
       grind)
    | exact superpose eq42535 eq50
    | exact resolve eq50 eq42535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq42535
  have eq42686 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq42620
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq42620
    | exact resolve eq42620 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42620
  have eq42706 : y = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq42577
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq42577
    | exact resolve eq42577 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42577
  have eq42741 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq42566
       grind)
    | exact superpose eq42566 eq81
    | exact resolve eq81 eq42566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42566
  have eq42775 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq42741
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq42741
    | exact resolve eq42741 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42741
  have eq43874 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq354
       have i₂ := eq42686
       grind)
    | exact superpose eq42686 eq354
    | exact resolve eq354 eq42686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42686
  have eq44024 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq43874
    | exact resolve eq43874 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43874
  have eq1143186 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) (M.op X0 X0)) ∨ (k (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4279 X0 X1 X2
       have i₂ := eq4014 (M.op X0 X0) X0 (M.op X1 X2)
       grind)
    | exact superpose eq4014 eq4279
    | (have j0 := eq4279 X0 X1 X2
       grind)
    | exact resolve eq4279 eq4014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4279
  have eq1144916 : (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) x) = (k (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) x) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) ∨ (M.op x y) = (k (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) := by
    first
    | (have i₁ := eq6387 (M.op sF0 sF0) sF0 sF0
       have i₂ := eq1143186 sF0 sF0 sF0
       grind)
    | exact superpose eq1143186 eq6387
    | (have j1 := eq1143186 (M.op x y) (M.op x y) (M.op x y)
       grind)
    | exact resolve eq6387 eq1143186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6387 eq1143186
  have eq1145515 : (M.op (M.op (M.op (M.op x y) (M.op x y)) x) x) = (k (M.op (M.op (M.op (M.op x y) (M.op x y)) x) x) (M.op (M.op (M.op x y) (M.op x y)) x)) ∨ (M.op x y) = (k (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) := by
    first
    | (have i₁ := eq1144916
       have i₂ := eq1667 sF0
       grind)
    | exact superpose eq1667 eq1144916
    | exact resolve eq1144916 eq1667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144916
  have eq1145966 : (M.op (M.op (M.op (M.op x y) x) x) x) = (k (M.op (M.op (M.op (M.op x y) x) x) x) (M.op (M.op (M.op x y) x) x)) ∨ (M.op x y) = (k (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq195 eq1145515
    | exact resolve eq1145515 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145515
  have eq1146299 : (M.op x y) = (k (M.op x y) (M.op (M.op (M.op x y) x) x)) ∨ (M.op x y) = (k (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq1479 eq1145966
    | exact resolve eq1145966 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479 eq1145966
  have eq1146534 : (M.op x y) = (k (M.op (M.op (M.op (M.op x y) (M.op x y)) x) (M.op (M.op x y) (M.op x y))) (M.op (M.op (M.op x y) (M.op x y)) x)) ∨ (M.op x y) = (k (M.op x y) (M.op (M.op (M.op x y) x) x)) := by
    first
    | (have i₁ := eq1146299
       have i₂ := eq1667 sF0
       grind)
    | exact superpose eq1667 eq1146299
    | exact resolve eq1146299 eq1667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667 eq1146299
  have eq1146718 : (M.op x y) = (k (M.op (M.op (M.op (M.op x y) x) x) (M.op (M.op x y) x)) (M.op (M.op (M.op x y) x) x)) ∨ (M.op x y) = (k (M.op x y) (M.op (M.op (M.op x y) x) x)) := by
    first
    | exact superpose eq195 eq1146534
    | exact resolve eq1146534 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq1146534
  have eq1146835 : (M.op x y) = (k (M.op (M.op (M.op (M.op x y) x) x) (M.op x y)) (M.op (M.op (M.op x y) x) x)) ∨ (M.op x y) = (k (M.op x y) (M.op (M.op (M.op x y) x) x)) := by
    first
    | (have i₁ := eq1146718
       have i₂ := eq4014 sF0 x x
       grind)
    | exact superpose eq4014 eq1146718
    | exact resolve eq1146718 eq4014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4014 eq1146718
  have eq1146930 : (M.op x y) = (k (M.op x y) (M.op (M.op (M.op x y) x) x)) ∨ (M.op x y) = (k (M.op x y) (M.op (M.op (M.op x y) x) x)) := by
    first
    | exact superpose eq1478 eq1146835
    | exact resolve eq1146835 eq1478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478 eq1146835
  have eq1146931 : (M.op x y) = (k (M.op x y) (M.op (M.op (M.op x y) x) x)) := by grind
  clear eq1146930
  have eq1811802 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq42775 eq38780
    | exact resolve eq38780 eq42775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1811893 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1811802 eq378
    | exact resolve eq378 eq1811802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1812072 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1811802 eq386
    | exact resolve eq386 eq1811802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811802
  have eq1812488 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq1812072
    | exact resolve eq1812072 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812072
  have eq1812556 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq1811893
    | exact resolve eq1811893 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811893
  have eq1812600 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq1812488
    | exact resolve eq1812488 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812488
  have eq1996639 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1812600 eq44024
    | exact resolve eq44024 eq1812600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812600
  have eq1996688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1996639
  have eq1996705 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1996688
       have r₂ := eq28
       grind)
    | exact resolve eq1996688 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996688
  have eq1996764 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1996705 eq2114
    | exact resolve eq2114 eq1996705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2114 eq1996705
  have eq1997535 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq1996764
    | exact resolve eq1996764 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996764
  have eq2675823 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1997535 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1997535
       grind)
    | exact resolve eq12 eq1997535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997535
  have eq2676163 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2675823
  have eq2676164 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2676163
  have eq2968076 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2676164 eq44024
    | exact resolve eq44024 eq2676164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2676164
  have eq2968125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2968076
  have eq2968142 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2968125
       have r₂ := eq28
       grind)
    | exact resolve eq2968125 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2968125
  have eq2968157 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2968142 eq28
    | exact resolve eq28 eq2968142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2968587 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2968142 eq1812556
    | exact resolve eq1812556 eq2968142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812556
  have eq2968994 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2968587
  have eq2969310 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq2968994
    | exact resolve eq2968994 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2968994
  have eq2969941 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2969310 eq2968142
    | exact resolve eq2968142 eq2969310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2968142 eq2969310
  have eq2969942 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2969941
  have eq2970635 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2969942 eq42775
    | exact resolve eq42775 eq2969942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42775 eq2969942
  have eq2970794 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2970635
       have r₂ := eq2968157
       grind)
    | exact resolve eq2970635 eq2968157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2970635
  have eq2974168 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2970794 eq44024
    | exact resolve eq44024 eq2970794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44024 eq2970794
  have eq2974224 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2974168
  have eq2974258 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2974224
       have r₂ := eq2968157
       grind)
    | exact resolve eq2974224 eq2968157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2968157 eq2974224
  have eq2974286 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2974258 eq30
    | exact resolve eq30 eq2974258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2974294 : (k y x) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2974258 eq91
    | exact resolve eq91 eq2974258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq2974491 : (k y x) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq124 eq2974294
    | exact resolve eq2974294 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq2974294
  have eq2974499 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq2974286
    | exact resolve eq2974286 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2974286
  have eq2974611 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2974499 eq1908
    | exact resolve eq1908 eq2974499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908 eq2974499
  have eq2976290 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2974611
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2974611
    | exact resolve eq2974611 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2974611
  have eq2977019 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq354
       have i₂ := eq2976290
       grind)
    | exact superpose eq2976290 eq354
    | exact resolve eq354 eq2976290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq2977384 : x = (M.op (M.op (M.op x y) x) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq378 x
       have i₂ := eq2976290
       grind)
    | exact superpose eq2976290 eq378
    | exact resolve eq378 eq2976290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2976290
  have eq2977894 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2977019
  have eq2978214 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq2977894
    | exact resolve eq2977894 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2977894
  have eq2983566 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2977384 eq1146931
    | exact resolve eq1146931 eq2977384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146931 eq2977384
  have eq2984543 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2983566 eq2974491
    | exact resolve eq2974491 eq2983566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2974491 eq2983566
  have eq2984569 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq2984543
  have eq2984670 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq2984569
       grind)
    | exact superpose eq2984569 eq81
    | exact resolve eq81 eq2984569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq2984569
  have eq2984773 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq2984670
    | exact resolve eq2984670 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2984670
  have eq2985096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2984773 eq38780
    | exact resolve eq38780 eq2984773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38780 eq2984773
  have eq2985159 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2985096
       have r₂ := eq28
       grind)
    | exact resolve eq2985096 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2985096
  have eq2985311 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2985159 eq378
    | exact resolve eq378 eq2985159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq2985514 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2985159 eq386
    | exact resolve eq386 eq2985159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq2985159
  have eq2986050 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq2985514
    | exact resolve eq2985514 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2985514
  have eq2986168 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq2985311
    | exact resolve eq2985311 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2985311
  have eq2986301 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq2986050
    | exact resolve eq2986050 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986050
  have eq3123277 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2986301 eq2978214
    | exact resolve eq2978214 eq2986301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2978214 eq2986301
  have eq3123335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3123277
  have eq3123359 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3123335
       have r₂ := eq28
       grind)
    | exact resolve eq3123335 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3123335
  have eq3124027 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3123359 eq2986168
    | exact resolve eq2986168 eq3123359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986168 eq3123359
  have eq3124090 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3124027
  have eq3124103 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq3124090
    | exact resolve eq3124090 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3124090
  have eq3124124 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3124103 eq28
    | exact resolve eq28 eq3124103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3124103
  have eq3124878 : x = (M.op x y) := by
    first
    | (have r₁ := eq3124124
       have r₂ := eq2974258
       grind)
    | exact resolve eq3124124 eq2974258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2974258 eq3124124
  have eq3124886 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3124878 eq21
    | exact resolve eq21 eq3124878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq3125298 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3124878 eq42706
    | exact resolve eq42706 eq3124878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42706
  have eq3126907 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3125298
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3125298
    | exact resolve eq3125298 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3125298
  have eq3127081 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3124886
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3124886
    | exact resolve eq3124886 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3124886
  have eq3127270 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3124878 eq3126907
    | exact resolve eq3126907 eq3124878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3126907
  have eq3127402 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3127081 eq27
    | exact resolve eq27 eq3127081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq3129278 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq3127270 eq30
    | exact resolve eq30 eq3127270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3127270
  have eq3129574 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq3129278
    | exact resolve eq3129278 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3129278
  have eq3129665 : x = y ∨ x = y := by
    first
    | exact superpose eq3124878 eq3129574
    | exact resolve eq3129574 eq3124878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3129574
  have eq3129666 : x = y := by grind
  clear eq3129665
  have eq3132351 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq3129666
       grind)
    | exact superpose eq3129666 eq19
    | exact resolve eq19 eq3129666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3132352 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq3129666
       grind)
    | exact superpose eq3129666 eq25
    | exact resolve eq25 eq3129666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3129666
  have eq3135087 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3132352
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3132352
    | exact resolve eq3132352 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3132352
  have eq3135088 : x = (M.op x x) := by
    first
    | exact superpose eq3124878 eq3132351
    | exact resolve eq3132351 eq3124878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3124878 eq3132351
  have eq3135745 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3127081 eq3135087
    | exact resolve eq3135087 eq3127081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3135087
  have eq3136180 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3135745 eq3127402
    | exact resolve eq3127402 eq3135745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3127402 eq3135745
  have eq3136845 : x = (k x x) := by grind
  clear eq3135088
  have eq3139746 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4872 x
       have i₂ := eq3136845
       grind)
    | exact superpose eq3136845 eq4872
    | (have j0 := eq4872 x
       grind)
    | exact resolve eq4872 eq3136845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4872 eq3136845
  have eq3139780 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3139746
  have eq3139803 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3139780
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3139780
    | exact resolve eq3139780 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3139780
  have eq3139855 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3127081 eq3139803
    | exact resolve eq3139803 eq3127081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3127081 eq3139803
  have eq3139903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3136180 eq3139855
    | exact resolve eq3139855 eq3136180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3136180 eq3139855
  have eq3139949 : False := by grind
  exact eq3139949

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation2659 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X0)) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq35 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq22
    | exact resolve eq22 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ X0)) := by
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
  have eq48 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq46
    | exact resolve eq46 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq70 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq137 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137 X0 X1 X2
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq137
    | (have j0 := eq137 X0 X1 X2
       grind)
    | exact resolve eq137 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq137
  have eq164 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq100 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq100
    | (have j0 := eq100 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq100 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq165 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq13 (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq13
    | (have j0 := eq13 (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)
       grind)
    | exact resolve eq13 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq165 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq165
    | (have j0 := eq165 X0
       grind)
    | exact resolve eq165 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq174 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) ∨ (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq168 X0
       have i₂ := eq15 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       grind)
    | exact superpose eq15 eq168
    | (have j0 := eq168 X0
       grind)
    | exact resolve eq168 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq178 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq174
    | (have j0 := eq174 X0
       grind)
    | exact resolve eq174 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq3454 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op X3 (k (σ X1) X2)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (k X3 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X3 ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (k (σ X0) X1)
       have i₂ := eq147 X0 X1 X2
       grind)
    | exact superpose eq147 eq13
    | (have j0 := eq13 (M.op (σ X0) (k (σ X1) X2)) (k X3 (k (σ X1) X2))
       have j1 := eq147 X1 X2 X0
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq147 X0 X1 X2
       grind)
    | exact resolve eq13 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq50931 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq164 X0
       grind)
    | exact superpose eq164 eq48
    | (have j1 := eq164 X0
       grind)
    | exact resolve eq48 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq164
  have eq51154 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq50931 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq50931
    | (have j0 := eq50931 X0
       grind)
    | exact resolve eq50931 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50931
  have eq51155 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have j0 := eq51154 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51154
  have eq63662 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq51155 X0
       grind)
    | exact superpose eq51155 eq178
    | (have j0 := eq178 X0
       have j1 := eq51155 X0
       grind)
    | (have r₁ := eq178 X0
       have r₂ := eq51155 X0
       grind)
    | exact resolve eq178 eq51155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq51155
  have eq63669 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq63662 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63662
  have eq63670 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have j0 := eq63669 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63669
  have eq86273 : ∀ X0 : G, (σ (τ X0)) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (σ (τ X0)) = (σ (k (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63670 (τ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq63670
    | exact resolve eq63670 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq63670
  have eq86560 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (σ (τ X0)) = (σ (k (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86273 X0
       have i₂ := eq30 (M.op X0 X0)
       grind)
    | exact superpose eq30 eq86273
    | (have j0 := eq86273 X0
       grind)
    | exact resolve eq86273 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86273
  have eq86568 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (σ (τ X0)) = (σ (k (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86560 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86560
    | (have j0 := eq86560 X0
       grind)
    | exact resolve eq86560 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86560
  have eq86573 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq86568 X0
       have i₂ := eq19 X0 (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))
       grind)
    | exact superpose eq19 eq86568
    | (have j0 := eq86568 X0
       grind)
    | exact resolve eq86568 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86568
  have eq86577 : ∀ X0 : G, (σ (τ X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq86573 X0
       have i₂ := eq30 (M.op X0 X0)
       grind)
    | exact superpose eq30 eq86573
    | (have j0 := eq86573 X0
       grind)
    | exact resolve eq86573 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq86573
  have eq86579 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq86577 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86577
    | (have j0 := eq86577 X0
       grind)
    | exact resolve eq86577 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86577
  have eq222477 : ∀ X0 X1 X2 : G, (k (σ X0) (k (σ X1) X2)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3454 X0 X1 X2 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3454
  have eq222478 : ∀ X0 X1 X2 : G, (k (σ X0) (k (σ X1) X2)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq222477 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222477
  have eq222484 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq222478 X0 X1 X2
       have i₂ := eq35 X1 X2 X0
       grind)
    | exact superpose eq35 eq222478
    | (have j0 := eq222478 X0 X1 X2
       grind)
    | exact resolve eq222478 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq222478
  have eq222485 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq222484 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222484
  have eq222975 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k X1 (τ X2))
       have i₂ := eq222485 (τ X0) X1 X2
       grind)
    | exact superpose eq222485 eq18
    | (have j1 := eq222485 (τ X0) X1 X2
       grind)
    | exact resolve eq18 eq222485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq222485
  have eq223332 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq222975 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq222975
    | (have j0 := eq222975 X0 X1 X2
       grind)
    | exact resolve eq222975 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222975
  have eq223512 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq223332 X0 X1 X2
       have i₂ := eq19 X2 X1
       grind)
    | exact superpose eq19 eq223332
    | (have j0 := eq223332 X0 X1 X2
       grind)
    | exact resolve eq223332 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223332
  have eq223631 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq223512 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq223512
    | (have j0 := eq223512 X0 X1 X2
       grind)
    | exact resolve eq223512 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223512
  have eq223919 : ∀ X0 X1 X2 : G, (k X1 (k X0 X2)) = (M.op X1 (k X0 X2)) ∨ (k X0 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq223631 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq223631
    | exact resolve eq223631 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223631
  have eq225238 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq225809 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq225238 (M.op X0 X0) X1
       have i₂ := eq86579 X0
       grind)
    | exact superpose eq86579 eq225238
    | (have j1 := eq86579 X0
       grind)
    | exact resolve eq225238 eq86579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86579 eq225238
  have eq257955 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq223919 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X0
       have i₂ := eq225809 X0 X1
       grind)
    | exact superpose eq225809 eq223919
    | (have j0 := eq223919 X1 (M.op X1 X0) X0
       have j1 := eq225809 X0 X1
       grind)
    | exact resolve eq223919 eq225809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223919 eq225809
  have eq260257 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq257955 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257955
  have eq260258 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq260257 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260257
  have eq260259 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq260258 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260258
  have eq260541 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq260259 X0 (τ X1)
       grind)
    | exact superpose eq260259 eq19
    | (have j1 := eq260259 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq260259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq260843 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq260259 (σ X0) (σ X1)
       grind)
    | exact superpose eq260259 eq15
    | (have j1 := eq260259 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq260259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260259
  have eq264428 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq260541 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq260541
    | exact resolve eq260541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260541
  have eq264952 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq264428 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq264428
    | (have j0 := eq264428 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq264428 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264428
  have eq269488 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq260843 x y
       grind)
    | exact superpose eq260843 eq16
    | (have j1 := eq260843 x y
       grind)
    | exact resolve eq16 eq260843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260843
  have eq269669 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq269488
       have i₂ := eq264952 y x
       grind)
    | exact superpose eq264952 eq269488
    | (have j1 := eq264952 (σ x) (σ y)
       grind)
    | (have r₁ := eq269488
       have r₂ := eq264952 y x
       grind)
    | (have r₁ := eq269488
       have r₂ := eq264952 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq269488
       have r₂ := eq264952 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq269488 eq264952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264952 eq269488
  have eq269672 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq269669
  have eq270320 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq269672
       grind)
    | exact superpose eq269672 eq16
    | exact resolve eq16 eq269672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269672
  have eq270321 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq270320
       have r₂ := eq22 x
       grind)
    | exact resolve eq270320 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270320
  have eq270322 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq270321
       grind)
    | exact superpose eq270321 eq16
    | exact resolve eq16 eq270321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270323 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq270321
       grind)
    | exact superpose eq270321 eq10
    | exact resolve eq10 eq270321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270321
  have eq270735 : x = y := by
    first
    | (have i₁ := eq270323
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq270323
    | exact resolve eq270323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270323
  have eq270736 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq270322
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq270322
    | exact resolve eq270322 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq270322
  have eq270743 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq270736
       have i₂ := eq270735
       grind)
    | exact superpose eq270735 eq270736
    | exact resolve eq270736 eq270735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270735 eq270736
  have eq270744 : False := by grind
  exact eq270744

/-- `Equation2676`: `x = ((x ◇ y) ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_pyx_pxy_y_pxy_Equation2676 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2676 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2676.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 x y X0
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 (M.op X1 X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X1 X2)) X1 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 (σ x) (σ y) X0
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq81 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op (M.op (M.op X0 x) x) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq81 eq54
    | exact resolve eq54 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq87 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq87 eq56
    | exact resolve eq56 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq105 (σ X0)
       grind)
    | exact superpose eq105 eq15
    | exact resolve eq15 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq124
    | exact resolve eq124 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq124
  have eq409 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq65
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq65
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq65 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq410 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq409
    | exact resolve eq409 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq414 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq410
    | exact resolve eq410 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq416 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq414
    | exact resolve eq414 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq466 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq53 X0 X1 x X2
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq53 (M.op X0 X1) X1 X2 x
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x
       have i₂ := eq53 sF0 y x x
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq476 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq57 x
       have i₂ := eq53 sF4 sF3 x x
       grind)
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq477 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X3)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op X1 X4)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X3)) X1 X4
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) y)) (M.op (M.op (M.op x y) y) X1)) = (M.op (M.op X0 x) (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | exact superpose eq473 eq53
    | exact resolve eq53 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1)) = (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq476 eq53
    | exact resolve eq53 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq466 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2)) X1 X2
       have i₂ := eq466 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq466 eq466
    | exact resolve eq466 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq466 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X3)) X1 X2
       have i₂ := eq9 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq9 eq466
    | exact resolve eq466 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X3)) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X1 X4)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X0 (M.op X1 X2)) X1) X1 X3 X4
       have i₂ := eq466 X0 X1 X2
       grind)
    | exact superpose eq466 eq53
    | exact resolve eq53 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq667 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op X0 (M.op X1 X2)) X1 x
       grind)
    | exact superpose eq9 eq667
    | exact resolve eq667 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq688 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = (M.op (M.op X0 x) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq520 X0 x
       have i₂ := eq645 X0 sF0 y x
       grind)
    | exact superpose eq645 eq520
    | exact resolve eq520 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq689 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq533 X0 x
       have i₂ := eq645 X0 sF4 sF3 x
       grind)
    | exact superpose eq645 eq533
    | exact resolve eq533 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq765 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq84 eq472
    | exact resolve eq472 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq90 eq472
    | exact resolve eq472 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X0 X2) X2)) (M.op (M.op (M.op X0 X2) X2) X3)) = (M.op (M.op X1 X0) (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 (M.op (M.op X0 X2) X2) X3 (M.op X2 x)
       have i₂ := eq472 X0 X2 x
       grind)
    | exact superpose eq472 eq53
    | exact resolve eq53 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq816 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X2)) = (M.op (M.op X1 X0) (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq814 X0 X1 X2 x
       have i₂ := eq645 X1 (M.op X0 X2) X2 x
       grind)
    | exact superpose eq645 eq814
    | exact resolve eq814 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq814
  have eq934 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op (M.op X0 X2) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq682 X1 (M.op (M.op X0 X2) X2) (M.op X2 x) X3
       have i₂ := eq472 X0 X2 x
       grind)
    | exact superpose eq472 eq682
    | exact resolve eq682 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq943 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 x) (M.op x y))) = (M.op X1 (M.op (M.op X0 (M.op x y)) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq81 eq682
    | exact resolve eq682 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1022 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X3) X4)) = (M.op (M.op X0 (M.op (M.op X1 X3) X5)) (M.op X1 X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 X0 (M.op X1 X3) X4 X5
       have i₂ := eq682 X0 X1 X2 X3
       grind)
    | (have i₁ := eq53 X0 (M.op X1 X3) X4 X5
       have i₂ := eq682 X0 X1 X3 X2
       grind)
    | exact superpose eq682 eq53
    | exact resolve eq53 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1058 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1022 X0 X1 X2 X3 X4 x
       have i₂ := eq644 X0 X1 X3 x
       grind)
    | exact superpose eq644 eq1022
    | exact resolve eq1022 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644 eq1022
  have eq2359 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op x y) X1)) x) (M.op (M.op x y) y)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq688 eq466
    | exact resolve eq466 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq2403 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq689 eq466
    | exact resolve eq466 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq2695 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X0 X2) X2)) = (M.op X1 (M.op (M.op X0 (M.op X2 X3)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq934 (M.op (M.op X0 X2) X2) X1 (M.op X2 X3) X4
       have i₂ := eq472 X0 X2 X3
       grind)
    | exact superpose eq472 eq934
    | exact resolve eq934 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3003 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op x y) X1) X3)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op x y) X1)) (M.op (M.op (M.op x y) X1) X2)) x) (M.op (M.op x y) y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2359 (M.op X0 (M.op (M.op sF0 X1) X3)) X1
       have i₂ := eq53 X0 (M.op sF0 X1) X2 X3
       grind)
    | exact superpose eq53 eq2359
    | exact resolve eq2359 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2359
  have eq3045 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op (M.op x y) X1) X3)) = (M.op (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) x) (M.op (M.op x y) y)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq3003 X0 X3 x X3
       have i₂ := eq1058 X0 sF0 X3 X3 x
       grind)
    | exact superpose eq1058 eq3003
    | exact resolve eq3003 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003
  have eq3074 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op (M.op x y) X1) X3)) = (M.op (M.op (M.op (M.op X0 (M.op x y)) x) (M.op x y)) (M.op (M.op x y) y)) := by
    intro X0 X1 X3
    first
    | exact superpose eq81 eq3045
    | exact resolve eq3045 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045
  have eq3086 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op (M.op x y) X1) X3)) = (M.op (M.op (M.op (M.op X0 (M.op x y)) x) x) x) := by
    intro X0 X1 X3
    first
    | exact superpose eq765 eq3074
    | exact resolve eq3074 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765 eq3074
  have eq3094 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op (M.op x y) X1) X3)) = (M.op (M.op (M.op (M.op X0 x) (M.op x y)) x) x) := by
    intro X0 X1 X3
    first
    | exact superpose eq81 eq3086
    | exact resolve eq3086 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3086
  have eq3101 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (M.op X0 x) x) (M.op x y)) x) = (M.op X0 (M.op (M.op (M.op x y) X1) X3)) := by
    intro X0 X1 X3
    first
    | exact superpose eq81 eq3094
    | exact resolve eq3094 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3094
  have eq3105 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (M.op X0 x) x) x) (M.op x y)) = (M.op X0 (M.op (M.op (M.op x y) X1) X3)) := by
    intro X0 X1 X3
    first
    | exact superpose eq81 eq3101
    | exact resolve eq3101 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq3101
  have eq3107 : ∀ X0 X1 X3 : G, (M.op X0 x) = (M.op X0 (M.op (M.op (M.op x y) X1) X3)) := by
    intro X0 X1 X3
    first
    | exact superpose eq84 eq3105
    | exact resolve eq3105 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3105
  have eq3665 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X3)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) (M.op (M.op (M.op (σ x) (σ y)) X1) X2)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2403 (M.op X0 (M.op (M.op sF4 X1) X3)) X1
       have i₂ := eq53 X0 (M.op sF4 X1) X2 X3
       grind)
    | exact superpose eq53 eq2403
    | exact resolve eq2403 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq2403
  have eq3712 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X3)) = (M.op (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq3665 X0 X3 x X3
       have i₂ := eq1058 X0 sF4 X3 X3 x
       grind)
    | exact superpose eq1058 eq3665
    | exact resolve eq3665 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3665
  have eq3741 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X3)) = (M.op (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X1 X3
    first
    | exact superpose eq87 eq3712
    | exact resolve eq3712 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3712
  have eq3755 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X3)) = (M.op (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) (σ x)) (σ x)) := by
    intro X0 X1 X3
    first
    | exact superpose eq768 eq3741
    | exact resolve eq3741 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq3741
  have eq3765 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X3)) = (M.op (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ x)) (σ x)) := by
    intro X0 X1 X3
    first
    | exact superpose eq87 eq3755
    | exact resolve eq3755 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3755
  have eq3773 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (M.op X0 (σ x)) (σ x)) (M.op (σ x) (σ y))) (σ x)) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X3)) := by
    intro X0 X1 X3
    first
    | exact superpose eq87 eq3765
    | exact resolve eq3765 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3765
  have eq3778 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X3)) := by
    intro X0 X1 X3
    first
    | exact superpose eq87 eq3773
    | exact resolve eq3773 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq3773
  have eq3781 : ∀ X0 X1 X3 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X3)) := by
    intro X0 X1 X3
    first
    | exact superpose eq90 eq3778
    | exact resolve eq3778 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3778
  have eq18196 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op x y)) X2)) (M.op (M.op (M.op X1 (M.op x y)) X2) X3)) (M.op (M.op (M.op X1 (M.op x y)) X2) X4)) (M.op (M.op X1 x) (M.op x y))) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) X2) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq943 eq477
    | exact resolve eq477 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq943
  have eq18245 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) X2) X5)) = (M.op (M.op (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op X1 (M.op x y))) (M.op (M.op (M.op X1 (M.op x y)) X2) X4)) (M.op (M.op X1 x) (M.op x y))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq18196 X0 X1 x X4 X4 X5
       have i₂ := eq1058 X0 (M.op X1 sF0) x x X4
       grind)
    | exact superpose eq1058 eq18196
    | exact resolve eq18196 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18196
  have eq18309 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) X2) X5)) = (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X1 (M.op x y)) (M.op x y))) (M.op (M.op (M.op X1 (M.op x y)) X2) X4)) (M.op (M.op X1 x) (M.op x y))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq18245 X1 X0 X2 X4 X5
       have i₂ := eq816 X0 X1 sF0
       grind)
    | exact superpose eq816 eq18245
    | exact resolve eq18245 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816 eq18245
  have eq18356 : ∀ X0 X1 X2 X5 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) X2) X5)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 (M.op x y))) (M.op X1 (M.op x y))) (M.op (M.op X1 x) (M.op x y))) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq18309 X0 X1 x x X5
       have i₂ := eq1058 (M.op X0 X1) (M.op X1 sF0) sF0 x x
       grind)
    | exact superpose eq1058 eq18309
    | exact resolve eq18309 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18309
  have eq18392 : ∀ X0 X1 X2 X5 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) X2) X5)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 (M.op x y))) X1) X1) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq18356 X0 X1 X2 X5
       have i₂ := eq1058 (M.op (M.op X0 X1) (M.op X1 sF0)) X1 sF0 x sF0
       grind)
    | exact superpose eq1058 eq18356
    | exact resolve eq18356 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058 eq18356
  have eq18415 : ∀ X0 X1 X2 X5 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) X2) X5)) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq18392 X0 X1 X2 X5
       have i₂ := eq466 (M.op X0 X1) X1 sF0
       grind)
    | exact superpose eq466 eq18392
    | exact resolve eq18392 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466 eq18392
  have eq18439 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 x) x)) = (M.op X1 (M.op (M.op X0 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq84 eq18415
    | exact resolve eq18415 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18557 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op X1 (M.op x y)) X3) X4)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq18415 eq934
    | exact resolve eq934 eq18415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934 eq18415
  have eq18652 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op (M.op X1 (M.op x y)) X3)) (M.op (M.op X1 (M.op x y)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18557 X0 X1 X1 X3 X3 x
       have i₂ := eq2695 (M.op X0 X1) X1 (M.op (M.op X1 sF0) X3) X3 x
       grind)
    | exact superpose eq2695 eq18557
    | exact resolve eq18557 eq2695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2695 eq18557
  have eq18826 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op (M.op X0 X1) x) x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18652 X0 X1 X1 x
       have i₂ := eq18439 (M.op X0 X1) X1 (M.op (M.op X1 sF0) x) (M.op (M.op X1 sF0) x)
       grind)
    | exact superpose eq18439 eq18652
    | exact resolve eq18652 eq18439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18652
  have eq19166 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 X2) x) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq682 X0 (M.op (M.op X1 X2) x) x X3
       have i₂ := eq18826 X1 X2 X0
       grind)
    | exact superpose eq18826 eq682
    | exact resolve eq682 eq18826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq18826
  have eq36603 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19166 X0 X1 X2 x
       have i₂ := eq18439 (M.op X1 X2) X0 X3 X4
       grind)
    | (have i₁ := eq19166 X1 X1 X2 X3
       have i₂ := eq18439 (M.op X1 X2) X1 x X3
       grind)
    | exact superpose eq18439 eq19166
    | exact resolve eq19166 eq18439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18439 eq19166
  have eq42700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq416
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq416
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq416 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq42734 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42700
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42700
    | exact resolve eq42700 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42700
  have eq42737 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq42734
    | exact resolve eq42734 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42734
  have eq42738 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq42737
       have r₂ := eq27
       grind)
    | exact resolve eq42737 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42737
  have eq42739 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42738
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42738
    | exact resolve eq42738 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42738
  have eq42740 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42739
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42739
    | exact resolve eq42739 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42739
  have eq42791 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ y) X0)) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq42740 eq472
    | exact resolve eq472 eq42740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42740
  have eq42808 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq476 eq42791
    | exact resolve eq42791 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq42791
  have eq42835 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq42808 eq90
    | exact resolve eq90 eq42808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42871 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X2)) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    intro X0 X1 X2
    first
    | exact superpose eq42808 eq36603
    | exact resolve eq36603 eq42808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42808
  have eq42873 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq3781 eq42871
    | exact resolve eq42871 eq3781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3781 eq42871
  have eq43811 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x y) y) (M.op y X0)) ∨ (M.op X1 (σ x)) = (M.op X1 (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq472 y y X0
       have i₂ := eq42873 X1
       grind)
    | exact superpose eq42873 eq472
    | (have j1 := eq42873 X1
       grind)
    | exact resolve eq472 eq42873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42873
  have eq43833 : ∀ X1 : G, (M.op X1 (σ x)) = (M.op X1 (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq473 eq43811
    | (have j0 := eq43811 x X1
       grind)
    | exact resolve eq43811 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43811
  have eq44117 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq43833 eq26
    | (have j1 := eq43833 (σ x)
       grind)
    | exact resolve eq26 eq43833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43833
  have eq44280 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq44117 eq90
    | exact resolve eq90 eq44117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq44117
  have eq44440 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq44280 eq42835
    | exact resolve eq42835 eq44280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42835 eq44280
  have eq44487 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq44440
  have eq44640 : ∀ X0 : G, y = (M.op (M.op (M.op x y) y) (M.op y X0)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq472 y y X0
       have i₂ := eq44487
       grind)
    | exact superpose eq44487 eq472
    | exact resolve eq472 eq44487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq44487
  have eq44657 : x = y ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq473 eq44640
    | exact resolve eq44640 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44640
  have eq44658 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq44657
  have eq44674 : x = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq473 x
       have i₂ := eq44658
       grind)
    | exact superpose eq44658 eq473
    | exact resolve eq473 eq44658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq44686 : y = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq84 y
       have i₂ := eq44658
       grind)
    | exact superpose eq44658 eq84
    | exact resolve eq84 eq44658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq44728 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op x y) X1) X2)) = (M.op X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36603 X0 y x X1 X2
       have i₂ := eq44658
       grind)
    | exact superpose eq44658 eq36603
    | exact resolve eq36603 eq44658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36603 eq44658
  have eq44731 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq3107 eq44728
    | exact resolve eq44728 eq3107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3107 eq44728
  have eq46358 : x = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44674
       have i₂ := eq44731 sF0
       grind)
    | exact superpose eq44731 eq44674
    | exact resolve eq44674 eq44731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44674 eq44731
  have eq46392 : x = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq46358
  have eq46700 : x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq46392 eq44686
    | exact resolve eq44686 eq46392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44686 eq46392
  have eq46751 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq46700
  have eq46789 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq46751 eq39
    | exact resolve eq39 eq46751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq46751
  have eq46849 : x = y ∨ x = y := by
    first
    | exact superpose eq38 eq46789
    | exact resolve eq46789 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq46789
  have eq46850 : x = y := by grind
  clear eq46849
  have eq46859 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq46850
       grind)
    | exact superpose eq46850 eq18
    | exact resolve eq18 eq46850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq46860 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq46850
       grind)
    | exact superpose eq46850 eq24
    | exact resolve eq24 eq46850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq46850
  have eq49110 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq46860
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46860
    | exact resolve eq46860 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46860
  have eq49455 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq49110 eq26
    | exact resolve eq26 eq49110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq49110
  have eq51627 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq125 x
       have i₂ := eq46859
       grind)
    | exact superpose eq46859 eq125
    | exact resolve eq125 eq46859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq46859
  have eq51692 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq51627
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51627
    | exact resolve eq51627 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq51627
  have eq52027 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49455 eq51692
    | exact resolve eq51692 eq49455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49455 eq51692
  have eq52164 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq52027
    | exact resolve eq52027 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq52027
  have eq52182 : False := by grind
  exact eq52182

/-- `Equation2688`: `x = ((x ◇ y) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(Y,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyy_x_pyx_pxy_pyx_Equation2688 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2688 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2688.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op X0 (M.op X3 X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X2 X2)) X1 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X2 X2)) (M.op X1 X1) X2
       have i₂ := eq9 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) ≠ X0 ∨ (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = (k (M.op (M.op X0 X1) (M.op X2 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X1) (M.op X2 X2)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op X0 X1) (M.op X2 X2)) X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) ≠ X0 ∨ (k (M.op (M.op X0 X1) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq22 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq24 (σ X0)
       grind)
    | exact superpose eq24 eq15
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq27
    | exact resolve eq27 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq31
    | (have j0 := eq31 X0 X1
       grind)
    | exact resolve eq31 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq35 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq24 (τ X0)
       grind)
    | exact superpose eq24 eq18
    | exact resolve eq18 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq40 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq41 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq40
    | exact resolve eq40 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq40
  have eq75 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 X2 (σ X0)
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq21
    | exact resolve eq21 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X4 X4)) = (M.op (M.op (M.op X0 (M.op X3 X3)) (M.op X5 X5)) X1) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq20 (M.op X0 (M.op X3 X3)) X1 X4 X5
       have i₂ := eq20 X0 X1 X2 X3
       grind)
    | (have i₁ := eq20 (M.op X0 X1) (M.op X2 X2) X2 X3
       have i₂ := eq20 X0 X1 X2 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X2) X3) (M.op X4 X4)) = (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 (M.op X0 X2) X3 X4 x
       have i₂ := eq20 X0 X2 x X1
       grind)
    | (have i₁ := eq20 (M.op X0 (M.op X3 X3)) X1 X2 X3
       have i₂ := eq20 X0 (M.op X3 X3) X2 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2 x
       have i₂ := eq20 X0 X2 x X1
       grind)
    | (have i₁ := eq9 X0 (M.op x x) X2
       have i₂ := eq20 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq20 (M.op X0 X1) X1 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq20 (M.op X0 (M.op X2 X2)) (M.op X2 X2) X2 x
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op X2 X2)) (M.op X0 (M.op X1 X1))) = (k (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op X2 X2)) (M.op X0 (M.op X1 X1))) ∨ (M.op (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op X2 X2)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op X2 X2))) := by
    intro X0 X1 X2
    grind
  have eq166 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op X2 X2)) (M.op X0 (M.op X1 X1))) = X0 ∨ (M.op (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op X2 X2)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq162 X0 X1 X2
       have i₂ := eq9 X0 (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq9 eq162
    | (have j0 := eq162 X0 X1 X2
       grind)
    | exact resolve eq162 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq167 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op X2 X2))) = X0 ∨ (k (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op X2 X2)) (M.op X0 (M.op X1 X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq166 X0 X1 X2
       have i₂ := eq9 X0 (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq9 eq166
    | (have j0 := eq166 X0 X1 X2
       grind)
    | exact resolve eq166 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq168 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op X2 X2)) (M.op X0 (M.op X1 X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq167 X0 X1 X2
       have j1 := eq25 X0 (M.op X0 (M.op X1 X1)) X2
       grind)
    | (have r₁ := eq167 X0 X1 X2
       have r₂ := eq25 X0 (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact resolve eq167 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq195 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq10
    | exact resolve eq10 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq245 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq32 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq32 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq32 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq32 X0 X1
       grind)
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq263 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq252 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq267 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq263 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq263
    | (have j0 := eq263 X0 X1
       grind)
    | exact resolve eq263 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq268 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq270 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq245 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq245
    | (have j0 := eq245 X0 X1
       grind)
    | exact resolve eq245 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq245
  have eq275 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq270 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq270 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq270 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq270 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq360 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (M.op X0 X1) X1 x
       have i₂ := eq156 X0 X1 x
       grind)
    | exact superpose eq156 eq25
    | exact resolve eq25 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq391 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq156 (τ X0) (τ X0) X1
       have i₂ := eq195 X0
       grind)
    | exact superpose eq195 eq156
    | exact resolve eq156 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq393 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (k (τ (M.op X0 X0)) (τ X0)) ∨ (M.op (τ (M.op X0 X0)) (τ X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  have eq404 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq393 X0
       have j1 := eq360 (τ (M.op X0 X0)) (τ X0)
       grind)
    | (have r₁ := eq393 X0
       have r₂ := eq360 (τ (M.op X0 X0)) (τ X0)
       grind)
    | (have r₁ := eq393 X0
       have r₂ := eq360 (τ X0) (τ (M.op X0 X0))
       grind)
    | exact resolve eq393 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq408 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq404 X0
       have i₂ := eq95 X0 (M.op X0 X0)
       grind)
    | exact superpose eq95 eq404
    | exact resolve eq404 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq404
  have eq409 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (k (M.op X0 X0) X0)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq391 X0 X1
       have i₂ := eq408 X0
       grind)
    | exact superpose eq408 eq391
    | exact resolve eq391 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq408
  have eq2096 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq275 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq275
    | (have j0 := eq275 X1 (τ X0)
       grind)
    | exact resolve eq275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq2121 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2096 X0 X1
       have i₂ := eq195 X0
       grind)
    | exact superpose eq195 eq2096
    | (have j0 := eq2096 X0 X1
       grind)
    | exact resolve eq2096 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq2096
  have eq2122 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2121 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2121
    | (have j0 := eq2121 X0 X1
       grind)
    | exact resolve eq2121 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2121
  have eq2412 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq268 x y
       grind)
    | exact superpose eq268 eq16
    | (have j1 := eq268 x y
       grind)
    | exact resolve eq16 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq3752 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (k (τ (M.op (σ X0) (σ X0))) X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq409 (σ X0) X1
       have i₂ := eq39 (M.op (σ X0) (σ X0)) X0
       grind)
    | exact superpose eq39 eq409
    | exact resolve eq409 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq409
  have eq3833 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (k (τ (σ (M.op X0 X0))) X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3752 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq3752
    | exact resolve eq3752 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3752
  have eq3857 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (k (M.op X0 X0) X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3833 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3833
    | exact resolve eq3833 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3833
  have eq3865 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) X0) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3857 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3857
    | exact resolve eq3857 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3857
  have eq4366 : ∀ X0 X1 : G, (σ X0) = (M.op (k (σ (M.op X0 X0)) (σ X0)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3865 (σ X0) X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq3865
    | exact resolve eq3865 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4414 : ∀ X0 X2 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X2) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq144 (k (M.op X0 X0) X0) x X2
       have i₂ := eq3865 X0 x
       grind)
    | exact superpose eq3865 eq144
    | exact resolve eq144 eq3865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq3865
  have eq4454 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k (M.op X0 X0) X0)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4366 X0 X1
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq4366
    | exact resolve eq4366 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4366
  have eq5472 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X2 X2)) X1)) (M.op X3 X3)) (M.op (M.op X0 (M.op X2 X2)) X1)) = (k (M.op (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X2 X2)) X1)) (M.op X3 X3)) (M.op (M.op X0 (M.op X2 X2)) X1)) ∨ (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X2 X2)) X1)) (M.op X3 X3)) (M.op (M.op X0 (M.op X2 X2)) X1)) = (M.op (M.op (M.op X0 (M.op X2 X2)) X1) (M.op (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X2 X2)) X1)) (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    grind
  have eq5577 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X2 X2)) X1)) (M.op X3 X3)) (M.op (M.op X0 (M.op X2 X2)) X1)) = (k (M.op (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X2 X2)) X1)) (M.op X3 X3)) (M.op (M.op X0 (M.op X2 X2)) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq5472 X0 X1 X2 X3
       have j1 := eq360 (M.op (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X2 X2)) X1)) (M.op X3 X3)) (M.op (M.op X0 (M.op X2 X2)) X1)
       grind)
    | (have r₁ := eq5472 X0 X1 X2 X3
       have r₂ := eq360 (M.op (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X2 X2)) X1)) (M.op X3 X3)) (M.op (M.op X0 (M.op X2 X2)) X1)
       grind)
    | (have r₁ := eq5472 X0 X1 X2 X3
       have r₂ := eq360 (M.op (M.op X0 (M.op X2 X2)) X1) (M.op (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X2 X2)) X1)) (M.op X3 X3))
       grind)
    | exact resolve eq5472 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq5472
  have eq5612 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k (M.op (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X2 X2)) X1)) (M.op X3 X3)) (M.op (M.op X0 (M.op X2 X2)) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5577 X0 X1 X2 X3
       have i₂ := eq9 (M.op X0 X1) (M.op (M.op X0 (M.op X2 X2)) X1) X3
       grind)
    | exact superpose eq9 eq5577
    | exact resolve eq5577 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5577
  have eq5642 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (M.op (σ X0) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4414 (σ X0) X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq4414
    | exact resolve eq4414 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4414
  have eq5836 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) X0)) = (M.op (M.op (σ X0) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5642 X0 X1
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq5642
    | exact resolve eq5642 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5642
  have eq10395 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X1)) = (k (M.op (M.op (M.op X0 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2))) (M.op X3 X3)) (M.op X4 X4)) (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq168 (M.op X0 (M.op X1 X1)) X2 X3
       have i₂ := eq134 X0 X1 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X3 X3) X4
       grind)
    | (have i₁ := eq168 (M.op X0 X2) X1 X4
       have i₂ := eq134 X0 X1 X2 (M.op (M.op X0 X2) (M.op X1 X1)) X4
       grind)
    | exact superpose eq134 eq168
    | exact resolve eq168 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24471 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 (M.op X1 X1))) = (M.op (σ (k (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op X2 X2)) (M.op X0 (M.op X1 X1)))) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4454 (M.op X0 (M.op X1 X1)) X3
       have i₂ := eq20 X0 (M.op X0 (M.op X1 X1)) X2 X1
       grind)
    | (have i₁ := eq4454 (M.op X2 X2) X1
       have i₂ := eq20 X2 X2 X2 X3
       grind)
    | exact superpose eq20 eq4454
    | exact resolve eq4454 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4454
  have eq24693 : ∀ X0 X1 X3 : G, (M.op (σ X0) (M.op X3 X3)) = (σ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq24471 X0 X1 x X3
       have i₂ := eq168 X0 X1 x
       grind)
    | exact superpose eq168 eq24471
    | exact resolve eq24471 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq24471
  have eq31124 : ∀ X0 X1 X2 X3 X4 X5 : G, (σ (k (M.op (M.op (M.op X0 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2))) (M.op X3 X3)) (M.op X4 X4)) (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)))) = (M.op (M.op (σ (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2))) X5) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq5836 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X5
       have i₂ := eq115 X0 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X3 X1 X4 X2
       grind)
    | (have i₁ := eq5836 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have i₂ := eq115 X1 X1 X1 X3 (M.op X1 X1) X5
       grind)
    | exact superpose eq115 eq5836
    | exact resolve eq5836 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq31125 : ∀ X0 X1 X2 X3 X4 : G, (σ (k (M.op (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X2 X2)) X1)) (M.op X3 X3)) (M.op (M.op X0 (M.op X2 X2)) X1))) = (M.op (M.op (σ (M.op (M.op X0 (M.op X2 X2)) X1)) X4) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5836 (M.op (M.op X0 (M.op X2 X2)) X1) X4
       have i₂ := eq134 X0 X2 X1 (M.op (M.op X0 (M.op X2 X2)) X1) X3
       grind)
    | (have i₁ := eq5836 (M.op (M.op X0 X2) (M.op X0 X2)) X1
       have i₂ := eq134 X0 X1 X2 (M.op X0 X2) (M.op X0 X2)
       grind)
    | exact superpose eq134 eq5836
    | exact resolve eq5836 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq5836
  have eq31506 : ∀ X0 X1 X2 X4 : G, (σ (M.op X0 X1)) = (M.op (M.op (σ (M.op (M.op X0 (M.op X2 X2)) X1)) X4) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq31125 X0 X1 X2 x X4
       have i₂ := eq5612 X0 X1 X2 x
       grind)
    | exact superpose eq5612 eq31125
    | exact resolve eq31125 eq5612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5612 eq31125
  have eq31507 : ∀ X0 X1 X2 X5 : G, (σ (M.op X0 (M.op X1 X1))) = (M.op (M.op (σ (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2))) X5) X5) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq31124 X0 X1 X2 x x X5
       have i₂ := eq10395 X0 X1 X2 x x
       grind)
    | exact superpose eq10395 eq31124
    | exact resolve eq31124 eq10395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10395 eq31124
  have eq31578 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X1))) = (σ (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31507 X0 X1 X2 x
       have i₂ := eq31506 X0 (M.op X2 X2) X1 x
       grind)
    | exact superpose eq31506 eq31507
    | exact resolve eq31507 eq31506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31506 eq31507
  have eq235354 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2412
       have i₂ := eq2122 x y
       grind)
    | exact superpose eq2122 eq2412
    | (have j1 := eq2122 x y
       grind)
    | exact resolve eq2412 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122 eq2412
  have eq235364 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq235354
  have eq240292 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq235364
       grind)
    | exact superpose eq235364 eq10
    | exact resolve eq10 eq235364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235364
  have eq240648 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq240292
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq240292
    | exact resolve eq240292 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240292
  have eq240649 : y = (M.op x x) := by grind
  clear eq240648
  have eq247850 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 x X1
       have i₂ := eq240649
       grind)
    | exact superpose eq240649 eq21
    | exact resolve eq21 eq240649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq247856 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 x X0 X1
       have i₂ := eq240649
       grind)
    | exact superpose eq240649 eq75
    | exact resolve eq75 eq240649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq248062 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X1))) = (σ (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq31578 X0 x X1
       have i₂ := eq240649
       grind)
    | exact superpose eq240649 eq31578
    | exact resolve eq31578 eq240649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31578 eq240649
  have eq248247 : ∀ X0 X3 : G, (M.op (σ X0) (M.op X3 X3)) = (σ (M.op X0 y)) := by
    intro X0 X3
    first
    | (have i₁ := eq24693 X0 x X3
       have i₂ := eq248062 X0 x
       grind)
    | exact superpose eq248062 eq24693
    | exact resolve eq24693 eq248062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24693 eq248062
  have eq311835 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq247856 X0 x
       have i₂ := eq247850 X0 x
       grind)
    | exact superpose eq247850 eq247856
    | exact resolve eq247856 eq247850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247856
  have eq334443 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq248247 X0 x
       have i₂ := eq247850 (σ X0) x
       grind)
    | exact superpose eq247850 eq248247
    | exact resolve eq248247 eq247850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247850 eq248247
  have eq375719 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq311835 (σ x)
       grind)
    | exact superpose eq311835 eq16
    | exact resolve eq16 eq311835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311835
  have eq441623 : False := by grind
  exact eq441623

/-- `Equation2734`: `x = ((y ◇ y) ◇ (x ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation2734 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2734 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2734.models_iff G M).mp hM
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
  clear eq22
  have eq265 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X2) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq270 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq272 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X2) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq265 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq273 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq271 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq271 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq284 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq273 (σ X0)
       grind)
    | exact superpose eq273 eq15
    | exact resolve eq15 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq284 X0
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq284
    | exact resolve eq284 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq284
  have eq348 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq272 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq552 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq551 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq567 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq552 (σ X1) (σ X0)
       grind)
    | exact superpose eq552 eq15
    | (have j1 := eq552 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq552 (τ X1) X0
       grind)
    | exact superpose eq552 eq17
    | (have j1 := eq552 (τ X1) X0
       grind)
    | exact resolve eq17 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq552
  have eq833 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq575 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq575
    | exact resolve eq575 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq913 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq833 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq833
    | (have j0 := eq833 X0 X1
       grind)
    | exact resolve eq833 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq1732 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq567 x y
       grind)
    | exact superpose eq567 eq16
    | (have j1 := eq567 x y
       grind)
    | exact resolve eq16 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1798 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq567 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq1932 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1798 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1798
    | (have j0 := eq1798 (τ X1) (τ X0)
       grind)
    | exact resolve eq1798 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1937 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1798 X0 X1
       have i₂ := eq913 X1 X0
       grind)
    | exact superpose eq913 eq1798
    | (have j0 := eq1798 X0 X1
       have j1 := eq913 (σ X1) (σ X0)
       grind)
    | exact resolve eq1798 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1940 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1932 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1932
    | (have j0 := eq1932 X0 X1
       grind)
    | exact resolve eq1932 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq1943 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1940 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1940
    | (have j0 := eq1940 X0 X1
       grind)
    | exact resolve eq1940 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq1944 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1943 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1943
    | (have j0 := eq1943 X0 X1
       grind)
    | exact resolve eq1943 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943
  have eq1945 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1944 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1944
    | (have j0 := eq1944 X0 X1
       grind)
    | exact resolve eq1944 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944
  have eq2042 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1732
       have i₂ := eq913 y x
       grind)
    | exact superpose eq913 eq1732
    | (have j1 := eq913 (σ y) (σ x)
       grind)
    | (have r₁ := eq1732
       have r₂ := eq913 y x
       grind)
    | exact resolve eq1732 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913 eq1732
  have eq2043 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2042
  have eq2046 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2043
       grind)
    | exact superpose eq2043 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2043
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2043
       grind)
    | exact resolve eq13 eq2043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043
  have eq2047 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq2046
  have eq3130 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2047
       grind)
    | exact superpose eq2047 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2047
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq2047
       grind)
    | exact resolve eq13 eq2047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2047
  have eq3131 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq3130
  have eq3132 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3131
       have i₂ := eq303 x
       grind)
    | exact superpose eq303 eq3131
    | exact resolve eq3131 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3131
  have eq3134 : x = (k y x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3132
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3132
    | exact resolve eq3132 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3132
  have eq214720 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1798 x y
       have i₂ := eq3134
       grind)
    | exact superpose eq3134 eq1798
    | (have j0 := eq1798 x y
       grind)
    | (have r₁ := eq1798 x y
       have r₂ := eq3134
       grind)
    | exact resolve eq1798 eq3134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3134
  have eq214832 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x x) := by grind
  clear eq214720
  have eq214835 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq1798 x y
       grind)
    | (have r₁ := eq214832
       have r₂ := eq1798 x y
       grind)
    | exact resolve eq214832 eq1798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798 eq214832
  have eq214838 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq214835
       grind)
    | exact superpose eq214835 eq16
    | exact resolve eq16 eq214835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214839 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq214835
       grind)
    | exact superpose eq214835 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq214835
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq214835
       grind)
    | exact resolve eq13 eq214835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214835
  have eq214840 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq214839
  have eq214841 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq1937 x x
       grind)
    | (have r₁ := eq214840
       have r₂ := eq1937 x x
       grind)
    | exact resolve eq214840 eq1937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937 eq214840
  have eq214843 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq214841
       have i₂ := eq303 x
       grind)
    | exact superpose eq303 eq214841
    | exact resolve eq214841 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303 eq214841
  have eq214844 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq214843
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq214843
    | exact resolve eq214843 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214843
  have eq214875 : (k y x) = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq214844
       grind)
    | exact superpose eq214844 eq10
    | exact resolve eq10 eq214844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214844
  have eq215105 : x = (k y x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq214875
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq214875
    | exact resolve eq214875 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214875
  have eq215139 : x ≠ x ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1945 y x
       have i₂ := eq215105
       grind)
    | exact superpose eq215105 eq1945
    | (have j0 := eq1945 y x
       grind)
    | (have r₁ := eq1945 y x
       have r₂ := eq215105
       grind)
    | exact resolve eq1945 eq215105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945 eq215105
  have eq215247 : x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq215139
  have eq215252 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq214838
       have i₂ := eq215247
       grind)
    | exact superpose eq215247 eq214838
    | exact resolve eq214838 eq215247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214838 eq215247
  have eq215261 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq215252
  have eq215262 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq215261
  have eq215370 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq215262
       grind)
    | exact superpose eq215262 eq10
    | exact resolve eq10 eq215262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215262
  have eq215606 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq215370
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq215370
    | exact resolve eq215370 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215370
  have eq215607 : x = (M.op x x) := by grind
  clear eq215606
  have eq215614 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq215607
       grind)
    | exact superpose eq215607 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq215607
       grind)
    | exact resolve eq12 eq215607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215624 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq348 x X0
       have i₂ := eq215607
       grind)
    | exact superpose eq215607 eq348
    | (have j0 := eq348 x X0
       grind)
    | exact resolve eq348 eq215607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq215607
  have eq215971 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq215624 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215624
  have eq215973 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq215614 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215614
  have eq217415 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq215971 (σ X0)
       grind)
    | exact superpose eq215971 eq15
    | exact resolve eq15 eq215971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215971
  have eq217688 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq217415 X0
       have i₂ := eq215973 X0
       grind)
    | exact superpose eq215973 eq217415
    | exact resolve eq217415 eq215973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215973 eq217415
  have eq221284 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq217688 y
       grind)
    | exact superpose eq217688 eq16
    | (have r₁ := eq16
       have r₂ := eq217688 y
       grind)
    | exact resolve eq16 eq217688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217688
  have eq221793 : False := by grind
  exact eq221793

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_pyy_pyx_Equation2755 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X1 X0) X1
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq21 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 X1
       have i₂ := eq23 (M.op X0 X0) X1
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op X1 X1) X0
       have i₂ := eq26 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq26 eq23
    | exact resolve eq23 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq32 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq12
    | (have r₁ := eq12 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq32 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq32 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X1) X0
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq12
    | (have j0 := eq12 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X0
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq12 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq98 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq101 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1
       have i₂ := eq26 X1 X0
       grind)
    | exact superpose eq26 eq98
    | exact resolve eq98 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq98
  have eq111 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq119 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq128 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq249 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X0
       have i₂ := eq32 X0 (σ X0)
       grind)
    | (have i₁ := eq111 X0 X0
       have i₂ := eq32 (σ X0) X1
       grind)
    | exact superpose eq32 eq111
    | exact resolve eq111 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq250 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq111 x y
       grind)
    | exact superpose eq111 eq16
    | (have j1 := eq111 x y
       grind)
    | exact resolve eq16 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq111 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq269 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq281 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq249 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq299 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq119 (M.op X1 X1) X0
       have i₂ := eq101 (σ X0) X1
       grind)
    | exact superpose eq101 eq119
    | exact resolve eq119 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq304 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq299 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq299
    | exact resolve eq299 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq848 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq269 (M.op X0 X0)
       have i₂ := eq101 (M.op X0 X0) X0
       grind)
    | exact superpose eq101 eq269
    | (have j0 := eq269 (M.op X0 X0)
       grind)
    | exact resolve eq269 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq269
  have eq877 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq848 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq1019 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X1)
       have i₂ := eq281 X0 (τ X1)
       grind)
    | exact superpose eq281 eq19
    | (have j1 := eq281 X0 (τ X1)
       grind)
    | exact resolve eq19 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1036 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq281 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq1060 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1019 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1019
    | (have j0 := eq1019 X0 X1
       grind)
    | exact resolve eq1019 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1090 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1060 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1060
    | (have j0 := eq1060 X0 X1
       grind)
    | exact resolve eq1060 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1099 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1090 X0 (k X1 X1)
       have j1 := eq65 X0 X1
       grind)
    | (have r₁ := eq1090 X0 X1
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq1090 X0 (M.op X0 X0)
       have r₂ := eq65 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq1090 X0 X1
       have r₂ := eq65 X0 (k X1 X1)
       grind)
    | exact resolve eq1090 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq1090
  have eq1221 : ∀ X0 X2 : G, (k (τ (k X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq304 X2 x
       have i₂ := eq1099 x X0
       grind)
    | exact superpose eq1099 eq304
    | exact resolve eq304 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1235 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X1
       have i₂ := eq1099 X1 X0
       grind)
    | exact superpose eq1099 eq23
    | exact resolve eq23 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq1256 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X1
       have i₂ := eq1099 X0 (σ X1)
       grind)
    | exact superpose eq1099 eq15
    | exact resolve eq15 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1265 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq128 X1 (σ X1)
       have i₂ := eq1099 X0 (σ X1)
       grind)
    | exact superpose eq1099 eq128
    | exact resolve eq128 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq1267 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X1)
       have i₂ := eq1099 X0 (τ X1)
       grind)
    | exact superpose eq1099 eq18
    | exact resolve eq18 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1099
  have eq1278 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1267 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1267
    | exact resolve eq1267 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq1279 : ∀ X0 X1 : G, (k X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1265 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1265
    | exact resolve eq1265 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq1585 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1235 (τ (M.op X0 X0)) X1
       have i₂ := eq304 (τ (M.op X0 X0)) X0
       grind)
    | exact superpose eq304 eq1235
    | exact resolve eq1235 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq1235
  have eq2983 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1221 X1 (τ (k X1 X1))
       have i₂ := eq1279 X0 (τ (k X1 X1))
       grind)
    | exact superpose eq1279 eq1221
    | exact resolve eq1221 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221 eq1279
  have eq3034 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq250
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq250
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq250 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq3035 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq3034
  have eq52296 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21 x y
       have i₂ := eq3035
       grind)
    | exact superpose eq3035 eq21
    | exact resolve eq21 eq3035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035
  have eq52308 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq52296
  have eq155950 : ∀ X0 X1 X2 : G, (σ X1) ≠ (M.op X0 X0) ∨ (σ X1) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1036 X2 X1
       have i₂ := eq1256 X0 X1
       grind)
    | exact superpose eq1256 eq1036
    | (have j0 := eq1036 X2 X1
       grind)
    | exact resolve eq1036 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036 eq1256
  have eq434574 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21 (σ x) (σ y)
       have i₂ := eq52308
       grind)
    | exact superpose eq52308 eq21
    | exact resolve eq21 eq52308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq52308
  have eq434595 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq434574
  have eq434648 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq877 x
       have i₂ := eq434595
       grind)
    | exact superpose eq434595 eq877
    | exact resolve eq877 eq434595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq434595
  have eq434901 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq155950 x y (σ y)
       grind)
    | (have r₁ := eq434648
       have r₂ := eq155950 (σ y) y x
       grind)
    | (have r₁ := eq434648
       have r₂ := eq155950 (σ x) y x
       grind)
    | exact resolve eq434648 eq155950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155950 eq434648
  have eq434967 : ∀ X0 : G, (k X0 X0) = (σ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1278 (σ y) X0
       have i₂ := eq434901
       grind)
    | exact superpose eq434901 eq1278
    | exact resolve eq1278 eq434901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq434986 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1585 (σ y) X0
       have i₂ := eq434901
       grind)
    | exact superpose eq434901 eq1585
    | exact resolve eq1585 eq434901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585
  have eq435046 : ∀ X0 : G, (τ (k X0 X0)) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2983 (σ y) X0
       have i₂ := eq434901
       grind)
    | exact superpose eq434901 eq2983
    | exact resolve eq2983 eq434901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2983 eq434901
  have eq435298 : ∀ X0 : G, y = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq435046 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq435046
    | exact resolve eq435046 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435046
  have eq435335 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq434986 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq434986
    | exact resolve eq434986 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434986
  have eq435432 : y = (τ (σ (σ y))) := by
    first
    | (have i₁ := eq435298 x
       have i₂ := eq434967 x
       grind)
    | exact superpose eq434967 eq435298
    | exact resolve eq435298 eq434967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434967 eq435298
  have eq435501 : y = (σ y) := by
    first
    | (have i₁ := eq435432
       have i₂ := eq10 (σ y)
       grind)
    | exact superpose eq10 eq435432
    | exact resolve eq435432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435432
  have eq438271 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq435501
       grind)
    | exact superpose eq435501 eq16
    | exact resolve eq16 eq435501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435501
  have eq438477 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq438271
       have i₂ := eq435335 (σ x)
       grind)
    | exact superpose eq435335 eq438271
    | exact resolve eq438271 eq435335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438271
  have eq438538 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq438477
       have i₂ := eq435335 x
       grind)
    | exact superpose eq435335 eq438477
    | exact resolve eq438477 eq435335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435335 eq438477
  have eq438539 : False := by grind
  exact eq438539

/-- `Equation2860`: `x = ((x ◇ (x ◇ y)) ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_y_pxy_y_pyx_Equation2860 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2860 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2860.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X2) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X0) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 (M.op X0 X1)) X2) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X1)) X2 (M.op (M.op X0 (M.op X0 X1)) X2)
       have i₂ := eq14 X0 X1 (M.op (M.op X0 (M.op X0 X1)) X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq10
    | exact resolve eq10 eq64
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
  have eq68 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq64 sF2
       grind)
    | exact superpose eq64 eq49
    | exact resolve eq49 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq68
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq68
    | exact resolve eq68 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
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
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq66
    | exact resolve eq66 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq100 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ (M.op x x) = (M.op y x) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ (M.op x x) = (M.op y x) := by
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
  have eq116 : (M.op x x) = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq256 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq64 (τ X0)
       grind)
    | exact superpose eq64 eq34
    | exact resolve eq34 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq267 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq256 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq256
    | exact resolve eq256 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq269 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq267 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq267
    | exact resolve eq267 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq267
  have eq548 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X0 (M.op X0 X1)) X2)) = (M.op (M.op X0 (M.op X0 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 (M.op X0 X1)) X2 (M.op (M.op X0 (M.op X0 X1)) X2)
       have i₂ := eq14 X0 X1 (M.op (M.op X0 (M.op X0 X1)) X2)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq16
    | exact resolve eq16 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq801 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X0 X2
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq811 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq71 X1
       grind)
    | exact superpose eq71 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq860 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq811 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq811
    | (have j0 := eq811 y X0
       grind)
    | exact resolve eq811 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq972 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq801 X0 x X3
       have i₂ := eq801 X0 x X1
       grind)
    | exact superpose eq801 eq801
    | exact resolve eq801 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq985 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x X0
       have i₂ := eq801 X0 x X1
       grind)
    | exact superpose eq801 eq14
    | exact resolve eq14 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq995 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X0 X1)) X0)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 (M.op X0 X2)
       have i₂ := eq801 X0 X1 (M.op X0 X2)
       grind)
    | exact superpose eq801 eq53
    | exact resolve eq53 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq1005 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq995 X0 X1 X2
       have i₂ := eq53 X0 X1 X0
       grind)
    | exact superpose eq53 eq995
    | exact resolve eq995 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq1057 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq985 (M.op X0 X0) X0
       have i₂ := eq985 X0 X0
       grind)
    | exact superpose eq985 eq985
    | exact resolve eq985 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1067 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X0) = (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op (M.op X0 X1) X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) X1) X0 X2
       have i₂ := eq985 X0 X1
       grind)
    | exact superpose eq985 eq53
    | exact resolve eq53 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1074 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1067 X0 X1 X2
       have i₂ := eq985 X0 X1
       grind)
    | exact superpose eq985 eq1067
    | exact resolve eq1067 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1197 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1057 (τ X0)
       have i₂ := eq646 X0
       grind)
    | exact superpose eq646 eq1057
    | exact resolve eq1057 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq1786 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq972 (M.op (M.op X0 X1) X1) X0 X2
       have i₂ := eq985 X0 X1
       grind)
    | exact superpose eq985 eq972
    | exact resolve eq972 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2050 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1005 X0 X0 X1
       have i₂ := eq1057 X0
       grind)
    | exact superpose eq1057 eq1005
    | exact resolve eq1005 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005 eq1057
  have eq4542 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq548 X0 x X2
       have i₂ := eq2050 X0 x
       grind)
    | exact superpose eq2050 eq548
    | exact resolve eq548 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq4543 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq4542 X0 x
       have i₂ := eq2050 (M.op X0 X0) x
       grind)
    | exact superpose eq2050 eq4542
    | exact resolve eq4542 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2050 eq4542
  have eq4546 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4543 (M.op X0 X0)
       have i₂ := eq4543 X0
       grind)
    | exact superpose eq4543 eq4543
    | exact resolve eq4543 eq4543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4551 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4543 (σ X0)
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq4543
    | exact resolve eq4543 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4605 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4551 X0
       have i₂ := eq71 (M.op X0 X0)
       grind)
    | exact superpose eq71 eq4551
    | exact resolve eq4551 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq4551
  have eq4610 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4546 X0
       have i₂ := eq1074 X0 X0 X0
       grind)
    | exact superpose eq1074 eq4546
    | exact resolve eq4546 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq4546
  have eq4612 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4605 X0
       have i₂ := eq4543 X0
       grind)
    | exact superpose eq4543 eq4605
    | exact resolve eq4605 eq4543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4543 eq4605
  have eq6424 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq860 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq860
    | (have j0 := eq860 x
       grind)
    | exact resolve eq860 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq6458 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6424
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq6424
    | exact resolve eq6424 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq6424
  have eq6473 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq6458
    | exact resolve eq6458 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6458
  have eq6482 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6473
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq6473
    | exact resolve eq6473 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq6473
  have eq25570 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4610 X1
       have i₂ := eq972 X1 X1 x
       grind)
    | (have i₁ := eq4610 x
       have i₂ := eq972 x X1 x
       grind)
    | exact superpose eq972 eq4610
    | exact resolve eq4610 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4610
  have eq32111 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X2) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1786 X0 X1 X1
       have i₂ := eq972 (M.op X0 X1) X1 X2
       grind)
    | (have i₁ := eq1786 X0 X1 X1
       have i₂ := eq972 (M.op X0 X1) X2 X1
       grind)
    | exact superpose eq972 eq1786
    | exact resolve eq1786 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972 eq1786
  have eq47102 : y = (M.op (M.op (M.op x x) x) (M.op (M.op x x) x)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq25570 y x
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq25570
    | exact resolve eq25570 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq47117 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (M.op (σ x) (σ x)) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq6482 eq25570
    | exact resolve eq25570 eq6482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6482
  have eq47296 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq47117
       have i₂ := eq25570 sF2 sF2
       grind)
    | exact superpose eq25570 eq47117
    | exact resolve eq47117 eq25570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47117
  have eq47305 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq47102
       have i₂ := eq25570 x x
       grind)
    | exact superpose eq25570 eq47102
    | exact resolve eq47102 eq25570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25570 eq47102
  have eq63245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq47305 eq47296
    | exact resolve eq47296 eq47305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47296 eq47305
  have eq63253 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq63245
       have r₂ := eq27
       grind)
    | exact resolve eq63245 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63245
  have eq63299 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) X0) X0) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq63253 eq32111
    | exact resolve eq32111 eq63253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63253
  have eq63301 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq63299 x
       have i₂ := eq985 sF2 x
       grind)
    | exact superpose eq985 eq63299
    | exact resolve eq63299 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63299
  have eq63691 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq63301 eq1197
    | exact resolve eq1197 eq63301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197 eq63301
  have eq63782 : x = (M.op (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq28 eq63691
    | exact resolve eq63691 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63691
  have eq63808 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq29 eq63782
    | exact resolve eq63782 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63782
  have eq63809 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq63808
  have eq63853 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op x X0) X0) x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq32111 y x X0
       have i₂ := eq63809
       grind)
    | exact superpose eq63809 eq32111
    | exact resolve eq32111 eq63809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32111 eq63809
  have eq63855 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq63853 x
       have i₂ := eq985 x x
       grind)
    | exact superpose eq985 eq63853
    | exact resolve eq63853 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985 eq63853
  have eq63903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4612 y
       have i₂ := eq63855
       grind)
    | exact superpose eq63855 eq4612
    | exact resolve eq4612 eq63855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4612 eq63855
  have eq63971 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq63903
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq63903
    | exact resolve eq63903 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63903
  have eq64003 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq63971
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq63971
    | exact resolve eq63971 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63971
  have eq64022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq64003
    | exact resolve eq64003 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64003
  have eq64029 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq64022
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq64022
    | exact resolve eq64022 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64022
  have eq64032 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq64029
    | exact resolve eq64029 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64029
  have eq64033 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq64032
       have r₂ := eq27
       grind)
    | exact resolve eq64032 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64032
  have eq64394 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq64033 eq29
    | exact resolve eq29 eq64033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq64033
  have eq64562 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq64394
    | exact resolve eq64394 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq64394
  have eq64563 : x = y := by grind
  clear eq64562
  have eq64595 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq64563
       grind)
    | exact superpose eq64563 eq18
    | exact resolve eq18 eq64563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq64596 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq64563
       grind)
    | exact superpose eq64563 eq24
    | exact resolve eq24 eq64563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq64563
  have eq64837 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq64596
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq64596
    | exact resolve eq64596 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq64596
  have eq64872 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq64837 eq26
    | exact resolve eq26 eq64837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq64837
  have eq65931 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq64872 eq69
    | exact resolve eq69 eq64872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq64872
  have eq66086 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq65931
       have i₂ := eq64595
       grind)
    | exact superpose eq64595 eq65931
    | exact resolve eq65931 eq64595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64595 eq65931
  have eq66110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66086 eq15
    | exact resolve eq15 eq66086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66086
  have eq66292 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq66110
    | exact resolve eq66110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq66110
  have eq66347 : False := by grind
  exact eq66347

/-- `Equation2880`: `x = ((x ◇ (y ◇ y)) ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_x_pxy_Equation2880 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X2) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
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
  have eq175 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X2 X3
       have i₂ := eq16 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X2 X2)) X1 (M.op X1 X1)
       have i₂ := eq16 X0 X2 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq574
       grind)
    | exact superpose eq574 eq41
    | exact resolve eq41 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq581 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq580
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq580
    | exact resolve eq580 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq583 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq581
    | exact resolve eq581 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq583 eq575
    | exact resolve eq575 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq583
  have eq600 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq593
       have r₂ := eq27
       grind)
    | exact resolve eq593 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq605 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq600 eq177
    | exact resolve eq177 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq600 eq605
    | exact resolve eq605 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600 eq605
  have eq613 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq610 eq153
    | exact resolve eq153 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq610
  have eq616 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq613
    | exact resolve eq613 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq613
  have eq619 : y = (M.op y y) := by
    first
    | (have j1 := eq576 y
       grind)
    | (have r₁ := eq616
       have r₂ := eq576 y
       grind)
    | exact resolve eq616 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq623 : (k y y) = (M.op y y) := by
    first
    | (have i₁ := eq177 y
       have i₂ := eq619
       grind)
    | exact superpose eq619 eq177
    | exact resolve eq177 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 y X1
       have i₂ := eq619
       grind)
    | exact superpose eq619 eq176
    | exact resolve eq176 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 y X1
       have i₂ := eq619
       grind)
    | exact superpose eq619 eq16
    | exact resolve eq16 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628 : y = (k y y) := by
    first
    | (have i₁ := eq623
       have i₂ := eq619
       grind)
    | exact superpose eq619 eq623
    | exact resolve eq623 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619 eq623
  have eq630 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq628
       grind)
    | exact superpose eq628 eq41
    | exact resolve eq41 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq628
  have eq633 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq630
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq630
    | exact resolve eq630 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq630
  have eq638 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq633 eq576
    | (have j0 := eq576 (σ y)
       grind)
    | (have r₁ := eq576 (σ y)
       have r₂ := eq633
       grind)
    | exact resolve eq576 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq639 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq638
  have eq646 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq639 eq176
    | exact resolve eq176 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq648 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ y)) X1) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq639 eq16
    | exact resolve eq16 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq639 eq625
    | exact resolve eq625 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq724 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq654 x
       grind)
    | exact superpose eq654 eq18
    | (have j1 := eq654 x
       grind)
    | exact resolve eq18 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq818 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X3 X3)) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 x (M.op X3 X3)
       have i₂ := eq175 X0 x X3 X1
       grind)
    | (have i₁ := eq16 X0 X1 (M.op X1 X1)
       have i₂ := eq175 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq832 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = (k (M.op X0 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0
       have i₂ := eq175 X0 X1 X2 X0
       grind)
    | (have i₁ := eq177 (M.op X2 X2)
       have i₂ := eq175 (M.op X2 X2) X2 X2 x
       grind)
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq845 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X1)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq832 X0 X1 x
       have i₂ := eq625 (M.op X0 (M.op X1 X1)) x
       grind)
    | exact superpose eq625 eq832
    | exact resolve eq832 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq855 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq818 X0 X1 x
       have i₂ := eq625 (M.op (M.op X0 X1) X1) x
       grind)
    | exact superpose eq625 eq818
    | exact resolve eq818 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq900 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X1)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq845 X0 X1
       have i₂ := eq654 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq654 eq845
    | exact resolve eq845 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq909 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (σ y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq855 X0 X1
       have i₂ := eq654 (M.op (M.op X0 X1) X1)
       grind)
    | exact superpose eq654 eq855
    | exact resolve eq855 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq949 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq900 X0 x
       have i₂ := eq625 X0 x
       grind)
    | exact superpose eq625 eq900
    | exact resolve eq900 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq988 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq949 X0
       have i₂ := eq654 X0
       grind)
    | exact superpose eq654 eq949
    | exact resolve eq949 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq1123 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) X2) = (M.op (M.op X0 X2) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq909 (M.op (M.op X0 (M.op X1 X1)) X2) X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq909
    | exact resolve eq909 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1130 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq909
    | (have j0 := eq909 (σ x) (σ y)
       grind)
    | exact resolve eq909 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1133 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq909 X0 X0
       have i₂ := eq177 X0
       grind)
    | exact superpose eq177 eq909
    | exact resolve eq909 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1140 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) X1) (σ y)) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq909 X0 X1
       have i₂ := eq28 (M.op X0 X1) X1
       grind)
    | exact superpose eq28 eq909
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq909 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1145 : ∀ X0 X1 : G, (M.op (k (k X0 X1) X1) (σ y)) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq28 eq1140
    | (have j0 := eq1140 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | exact resolve eq1140 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1151 : (σ x) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq988 eq1130
    | exact resolve eq1130 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq1157 : ∀ X0 X2 : G, (M.op (M.op X0 y) X2) = (M.op (M.op X0 X2) (σ y)) := by
    intro X0 X2
    first
    | (have i₁ := eq1123 X0 x X2
       have i₂ := eq625 X0 x
       grind)
    | exact superpose eq625 eq1123
    | exact resolve eq1123 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625 eq1123
  have eq1171 : ∀ X0 X2 : G, (M.op (M.op X0 (σ y)) X2) = (M.op (M.op X0 X2) (σ y)) := by
    intro X0 X2
    first
    | (have i₁ := eq1157 X0 X2
       have i₂ := eq654 X0
       grind)
    | exact superpose eq654 eq1157
    | exact resolve eq1157 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq1157
  have eq1229 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq627 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq627
    | (have j0 := eq627 x X0
       grind)
    | exact resolve eq627 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq627
  have eq1355 : ∀ X0 : G, x = (k (M.op (M.op x y) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1229 eq28
    | (have j0 := eq28 X0 X0
       grind)
    | exact resolve eq28 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1370 : ∀ X0 : G, x = (k (k (M.op x y) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq1355
    | (have j0 := eq1355 X0
       have j1 := eq28 X0 X0
       grind)
    | exact resolve eq1355 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1355
  have eq1907 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq1133 eq648
    | exact resolve eq648 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1910 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq26 eq648
    | (have j0 := eq648 (σ x) X0
       grind)
    | exact resolve eq648 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2060 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq1910 eq909
    | exact resolve eq909 eq1910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1910
  have eq2945 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op (k (M.op X0 X0) X0) X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq988 eq648
    | exact resolve eq648 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648 eq988
  have eq3030 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (σ y)) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1171 eq909
    | exact resolve eq909 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3161 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op (M.op X0 X1) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq3030 eq1171
    | exact resolve eq1171 eq3030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq8296 : (σ x) = (k (σ (k (M.op x y) x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1370 eq40
    | (have j1 := eq1370 x
       grind)
    | exact resolve eq40 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq8310 : (σ x) = (k (k (σ (M.op x y)) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8296
       have i₂ := eq40 sF0
       grind)
    | exact superpose eq40 eq8296
    | exact resolve eq8296 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8296
  have eq8323 : (σ x) = (k (k (σ (M.op x y)) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq8310
    | exact resolve eq8310 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8310
  have eq8330 : (σ x) = (k (k (σ (M.op x y)) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8323
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8323
    | exact resolve eq8323 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8323
  have eq20170 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ y)) (σ y)) X1) = (M.op (k (M.op X0 X0) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3030 (M.op (k (M.op X0 X0) X0) X1) X1
       have i₂ := eq2945 X0 X1
       grind)
    | exact superpose eq2945 eq3030
    | exact resolve eq3030 eq2945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2945 eq3030
  have eq27297 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8330 eq1145
    | (have j0 := eq1145 x (σ x)
       grind)
    | exact resolve eq1145 eq8330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145 eq8330
  have eq27358 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq27297
    | exact resolve eq27297 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27297
  have eq27409 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq27358
       have r₂ := eq27
       grind)
    | exact resolve eq27358 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27358
  have eq27441 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27409 eq2060
    | exact resolve eq2060 eq27409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27466 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27409 eq909
    | exact resolve eq909 eq27409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq27480 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2060 eq27466
    | exact resolve eq27466 eq2060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060 eq27466
  have eq27493 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq27441
    | exact resolve eq27441 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27441
  have eq27515 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27480 eq27493
    | exact resolve eq27493 eq27480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27480 eq27493
  have eq27596 : (k x x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1907 x x
       have i₂ := eq27515
       grind)
    | exact superpose eq27515 eq1907
    | exact resolve eq1907 eq27515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907
  have eq27608 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27515 eq27596
    | exact resolve eq27596 eq27515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27515 eq27596
  have eq27754 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq27608
       grind)
    | exact superpose eq27608 eq40
    | exact resolve eq40 eq27608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq27608
  have eq27764 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27754
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27754
    | exact resolve eq27754 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27754
  have eq28203 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27764 eq576
    | (have j0 := eq576 (σ x)
       grind)
    | (have r₁ := eq576 (σ x)
       have r₂ := eq27764
       grind)
    | exact resolve eq576 eq27764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28210 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28203
  have eq28401 : (σ x) = (M.op (k (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28210 eq1133
    | exact resolve eq1133 eq28210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28210
  have eq28427 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27764 eq28401
    | exact resolve eq28401 eq27764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27764 eq28401
  have eq28458 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28427
    | exact resolve eq28427 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq28427
  have eq28459 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28458
  have eq28486 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq28459 eq27
    | exact resolve eq27 eq28459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq28487 : (σ x) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | exact superpose eq28459 eq1151
    | exact resolve eq1151 eq28459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151 eq28459
  have eq28545 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq28487 eq142
    | exact resolve eq142 eq28487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq28487
  have eq28548 : x = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq30 eq28545
    | exact resolve eq28545 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28545
  have eq28711 : x = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27409 eq28548
    | exact resolve eq28548 eq27409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27409 eq28548
  have eq28724 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq28711
    | exact resolve eq28711 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq28711
  have eq28729 : x = (M.op x x) := by
    first
    | (have j1 := eq576 x
       grind)
    | (have r₁ := eq28724
       have r₂ := eq576 x
       grind)
    | exact resolve eq28724 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq28724
  have eq28757 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq646 X0 x
       have i₂ := eq28729
       grind)
    | exact superpose eq28729 eq646
    | exact resolve eq646 eq28729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq28775 : (M.op x (σ y)) = (M.op (M.op (M.op x (σ y)) (σ y)) x) := by
    first
    | (have i₁ := eq3161 x x
       have i₂ := eq28729
       grind)
    | exact superpose eq28729 eq3161
    | exact resolve eq3161 eq28729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3161 eq28729
  have eq28781 : (M.op x (σ y)) = (M.op (k (M.op x x) x) x) := by
    first
    | exact superpose eq20170 eq28775
    | exact resolve eq28775 eq20170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20170 eq28775
  have eq28816 : (M.op x (σ y)) = (M.op (k (M.op x x) x) (σ y)) := by
    first
    | (have i₁ := eq28781
       have i₂ := eq28757 (k (M.op x x) x)
       grind)
    | exact superpose eq28757 eq28781
    | exact resolve eq28781 eq28757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28757 eq28781
  have eq28839 : x = (M.op x (σ y)) := by
    first
    | exact superpose eq1133 eq28816
    | exact resolve eq28816 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133 eq28816
  have eq28858 : x = (M.op x y) := by
    first
    | exact superpose eq724 eq28839
    | exact resolve eq28839 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq28839
  have eq28878 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq28858
       grind)
    | exact superpose eq28858 eq22
    | exact resolve eq22 eq28858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq28858
  have eq28960 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28878 eq20
    | exact resolve eq20 eq28878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq28878
  have eq28979 : False := by grind
  exact eq28979
