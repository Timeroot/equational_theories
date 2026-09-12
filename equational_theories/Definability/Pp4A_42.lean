import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3201`: `x = (((y ◇ z) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_x_pxy_y_pyx_Equation3201 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3201 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3201.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X1) X2) X0) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) y) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X2) X1) X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = (k X0 (M.op (M.op (M.op X1 X2) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X1) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 (M.op (M.op (M.op X1 X2) X1) X2)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X1) X2)
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = (k X0 (M.op (M.op (M.op X1 X2) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq65 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) X1) ≠ (M.op (M.op (M.op X0 X1) X0) X1) ∨ (M.op (M.op (M.op X0 X1) X0) X1) = (M.op X2 (M.op (M.op (M.op X0 X1) X0) X1)) ∨ (k (M.op (M.op (M.op X0 X1) X0) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op (M.op X0 X1) X0) X1) X2
       have i₂ := eq14 (M.op (M.op (M.op X0 X1) X0) X1) X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op (M.op X0 X1) X0) X1) X2
       grind)
    | (have r₁ := eq12 (M.op (M.op (M.op X1 X2) X1) X2) X1
       have r₂ := eq14 (M.op (M.op (M.op X1 X2) X1) X2) X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op X2 (M.op (M.op (M.op X0 X1) X0) X1)) ∨ (k (M.op (M.op (M.op X0 X1) X0) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq76 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq95 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112
    | exact resolve eq112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq237 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq700 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq93 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq702 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq700 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq836 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) X1) ≠ (M.op (M.op (M.op X0 X1) X0) X1) ∨ (M.op (M.op (M.op (M.op X0 X1) X0) X1) X2) = (k (M.op (M.op (M.op X0 X1) X0) X1) X2) ∨ (k (M.op (M.op (M.op X0 X1) X0) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op (M.op X0 X1) X0) X1) X2
       have i₂ := eq77 X0 X1 X2
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 (M.op (M.op (M.op X0 X1) X0) X1) X2
       have j1 := eq77 X0 X1 X2
       grind)
    | (have r₁ := eq13 (M.op (M.op (M.op X0 X1) X0) X1) X2
       have r₂ := eq77 X0 X1 X2
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq847 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X1) X2) = (k (M.op (M.op (M.op X0 X1) X0) X1) X2) ∨ (k (M.op (M.op (M.op X0 X1) X0) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq836 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq852 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X1) X0) X1) X2) = X2 ∨ (k (M.op (M.op (M.op X0 X1) X0) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq847 X0 X1 X2
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq847
    | (have j0 := eq847 X0 X1 X2
       grind)
    | exact resolve eq847 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq853 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X1) X0) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq852 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq884 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (M.op (M.op (M.op X1 X2) X1) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq237 (M.op (M.op (M.op X1 X2) X1) X2) X0
       have i₂ := eq853 X1 X2 (σ X0)
       grind)
    | exact superpose eq853 eq237
    | exact resolve eq237 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq885 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (M.op (M.op (M.op X1 X2) X1) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 (M.op (M.op (M.op X1 X2) X1) X2)
       have i₂ := eq853 X1 X2 (τ X0)
       grind)
    | exact superpose eq853 eq38
    | exact resolve eq38 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq886 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op (M.op X1 X2) X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq885 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq885
    | exact resolve eq885 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq887 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op (M.op X1 X2) X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq884 X0 X1 X2
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq884
    | exact resolve eq884 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq3863 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq702 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq702
    | (have j0 := eq702 (τ X0)
       grind)
    | exact resolve eq702 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3884 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3863 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3863
    | (have j0 := eq3863 X0
       grind)
    | exact resolve eq3863 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3863
  have eq3901 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3884 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3884
    | (have j0 := eq3884 X0
       grind)
    | exact resolve eq3884 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3884
  have eq5111 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq95 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95
    | (have j0 := eq95 y
       grind)
    | exact resolve eq95 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq5123 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5111
  have eq5126 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5123
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq5123
    | exact resolve eq5123 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq5123
  have eq5150 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq5126
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq5126 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5126
  have eq5166 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5150 eq87
    | exact resolve eq87 eq5150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq5150
  have eq14998 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq14999 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq14998
    | exact resolve eq14998 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14998
  have eq15010 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq14999
       have r₂ := eq27
       grind)
    | exact resolve eq14999 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14999
  have eq15012 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq15010
    | exact resolve eq15010 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15010
  have eq15999 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq15012 eq5166
    | exact resolve eq5166 eq15012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5166 eq15012
  have eq16026 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq15999
    | exact resolve eq15999 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15999
  have eq16029 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3901 y
       grind)
    | (have r₁ := eq16026
       have r₂ := eq3901 y
       grind)
    | exact resolve eq16026 eq3901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3901 eq16026
  have eq16032 : ∀ X0 : G, (M.op (M.op (M.op y y) y) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq16029
       grind)
    | exact superpose eq16029 eq14
    | exact resolve eq14 eq16029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16029
  have eq16491 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq16032 y
       grind)
    | exact superpose eq16032 eq14
    | exact resolve eq14 eq16032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16492 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X0) X1) = X1 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 y y X1
       have i₂ := eq16032 y
       grind)
    | exact superpose eq16032 eq52
    | exact resolve eq52 eq16032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16493 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq66 X0 y y
       have i₂ := eq16032 y
       grind)
    | exact superpose eq16032 eq66
    | exact resolve eq66 eq16032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16503 : ∀ X0 : G, (k (σ y) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq886 X0 y y
       have i₂ := eq16032 y
       grind)
    | exact superpose eq16032 eq886
    | exact resolve eq886 eq16032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886 eq16032
  have eq16569 : ∀ X0 : G, (k (σ y) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16503 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16503
    | (have j0 := eq16503 X0
       grind)
    | exact resolve eq16503 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16503
  have eq19388 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq16493 x
       grind)
    | exact superpose eq16493 eq44
    | exact resolve eq44 eq16493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq19431 : y = (M.op (σ y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16569 y
       have i₂ := eq16493 sF3
       grind)
    | exact superpose eq16493 eq16569
    | exact resolve eq16569 eq16493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16493 eq16569
  have eq19454 : y = (M.op (σ y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19431
  have eq19493 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19388
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19388
    | exact resolve eq19388 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19388
  have eq19509 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq19493
    | exact resolve eq19493 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19493
  have eq29022 : ∀ X0 : G, (M.op (M.op y (σ y)) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19454 eq16492
    | exact resolve eq16492 eq19454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16492 eq19454
  have eq29141 : ∀ X0 : G, (M.op (M.op y (σ y)) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq29022 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29022
  have eq29386 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq29141 X0
       have i₂ := eq16491 sF3
       grind)
    | exact superpose eq16491 eq29141
    | exact resolve eq29141 eq16491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16491 eq29141
  have eq29446 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq29386 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29386
  have eq29734 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq29446 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq29446 X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq29446 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq29446 X0
       grind)
    | exact resolve eq13 eq29446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29446
  have eq29776 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq29734 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29734
  have eq30271 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29776 eq19509
    | exact resolve eq19509 eq29776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19509 eq29776
  have eq30365 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq30271
  have eq30402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq30365
    | exact resolve eq30365 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30365
  have eq30414 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq30402
       have r₂ := eq27
       grind)
    | exact resolve eq30402 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30402
  have eq30417 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30414 eq51
    | exact resolve eq51 eq30414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq30414
  have eq31467 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f31467_14 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 ∨ y = (M.op x y) := by
      intro X0
      grind
    have f31467_20 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X1) X2) X0) = X0 := by
      intro X0 X1 X2
      grind
    have f31467_23 : X0 ≠ (M.op (σ x) X0) := by grind
    have f31467_24 : y ≠ (M.op x y) := by grind
    have f31467_25 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 := by
      intro X0
      first
      | (have j0 := f31467_14 X0
         grind)
      | (have r₁ := f31467_14 X0
         have r₂ := f31467_24
         grind)
      | exact resolve f31467_14 f31467_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f31467_53 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
      intro X0
      first
      | (have i₁ := f31467_20 X0 (σ y) (σ x)
         have i₂ := f31467_25 (σ x)
         grind)
      | exact superpose f31467_25 f31467_20
      | exact resolve f31467_20 f31467_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f31467_57 : X0 ≠ X0 := by
      first
      | (have i₁ := f31467_23
         have i₂ := f31467_53 X0
         grind)
      | exact superpose f31467_53 f31467_23
      | (have r₁ := f31467_23
         have r₂ := f31467_53 X0
         grind)
      | exact resolve f31467_23 f31467_53
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f31467_62 : False := by grind
    exact f31467_62
  have eq31468 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ x)) X0) X1) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq30417 eq52
    | exact resolve eq52 eq30417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq31469 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30417 eq66
    | exact resolve eq66 eq30417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq31480 : ∀ X0 : G, (k (τ (σ x)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30417 eq887
    | exact resolve eq887 eq30417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq30417
  have eq31551 : ∀ X0 : G, (k x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq31480
    | exact resolve eq31480 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq31480
  have eq33229 : (σ x) = (M.op x (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31469 eq31551
    | exact resolve eq31551 eq31469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31469 eq31551
  have eq33268 : (σ x) = (M.op x (σ x)) ∨ y = (M.op x y) := by grind
  clear eq33229
  have eq43834 : ∀ X0 : G, (M.op (M.op (σ x) x) X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33268 eq31468
    | exact resolve eq31468 eq33268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31468 eq33268
  have eq43960 : ∀ X0 : G, (M.op (M.op (σ x) x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq43834 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43834
  have eq44128 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31467 eq43960
    | exact resolve eq43960 eq31467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31467 eq43960
  have eq44190 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq44128 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44128
  have eq44221 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq44190 y
       grind)
    | exact superpose eq44190 eq18
    | (have j1 := eq44190 y
       grind)
    | exact resolve eq18 eq44190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq44190
  have eq44273 : y = (M.op x y) := by grind
  clear eq44221
  have eq44304 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq44273 eq20
    | exact resolve eq20 eq44273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq44306 : ∀ X0 : G, (M.op (M.op (M.op y x) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq44273 eq50
    | exact resolve eq50 eq44273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq44273
  have eq44442 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq44304
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44304
    | exact resolve eq44304 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq44304
  have eq44479 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq44442 eq26
    | exact resolve eq26 eq44442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq44442
  have eq45280 : ∀ X0 : G, (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq853 y x X0
       have i₂ := eq44306 x
       grind)
    | exact superpose eq44306 eq853
    | exact resolve eq853 eq44306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853 eq44306
  have eq45460 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq702 x
       have i₂ := eq45280 x
       grind)
    | exact superpose eq45280 eq702
    | (have j0 := eq702 x
       grind)
    | exact resolve eq702 eq45280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq45280
  have eq45547 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq45460
  have eq45614 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq45547
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45547
    | exact resolve eq45547 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq45547
  have eq46056 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq45614 eq14
    | exact resolve eq14 eq45614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46087 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq45614 eq46056
    | exact resolve eq46056 eq45614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46056
  have eq46111 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq45614 eq46087
    | exact resolve eq46087 eq45614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45614 eq46087
  have eq46135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46111 eq44479
    | exact resolve eq44479 eq46111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44479 eq46111
  have eq46229 : False := by grind
  exact eq46229

/-- `Equation3263`: `x ◇ x = x ◇ (y ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_Equation3263 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3263 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3263.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq117 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq117 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq117 X0 X1
       grind)
    | exact superpose eq117 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq117 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq117 X0 X1
       grind)
    | exact resolve eq12 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq117 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq117 X0 X1
       grind)
    | exact superpose eq117 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq117 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq117 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq117 X0 X1
       grind)
    | exact resolve eq13 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq768 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq758 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq775 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq768 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq768 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq768 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq768 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq776 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq757 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq757 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq757 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq794 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq775 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq775
    | (have j0 := eq775 X0 X1
       grind)
    | exact resolve eq775 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq795 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq794 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq796 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq776 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq776
    | (have j0 := eq776 X0 X1
       grind)
    | exact resolve eq776 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq797 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq796 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq808 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq797 X0 X1
       have j1 := eq795 X0 X1
       grind)
    | (have r₁ := eq797 X0 X1
       have r₂ := eq795 X0 X1
       grind)
    | exact resolve eq797 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795 eq797
  have eq812 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq808 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq808
    | exact resolve eq808 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq829 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq808 x y
       grind)
    | exact superpose eq808 eq16
    | exact resolve eq16 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq1044 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq812 X0 (τ X1)
       grind)
    | exact superpose eq812 eq18
    | exact resolve eq18 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq812
  have eq1057 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1044 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1044
    | exact resolve eq1044 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1067 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1057 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1057
    | exact resolve eq1057 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1087 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq829
       have i₂ := eq1067 x y
       grind)
    | exact superpose eq1067 eq829
    | exact resolve eq829 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829 eq1067
  have eq1088 : False := by grind
  exact eq1088

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pxy_y_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X1 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X1 X3 X4
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
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
  have eq26 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X1 X2)) ∨ (k (M.op X0 (M.op X1 X2)) X1) = (M.op (M.op X0 (M.op X1 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 (M.op X1 X2)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X0 (M.op X1 X2)) X1
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X2) (M.op X1 X2)) X1
       have r₂ := eq9 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X2 X3))) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X2 X3))) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq31 X0 X1 X2 X3
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq31 (M.op X1 (M.op X1 X3)) X1 X1 X3
       have r₂ := eq12 (M.op X1 (M.op X1 X3)) X1
       grind)
    | (have r₁ := eq31 (M.op X1 (M.op X2 (M.op X1 (M.op X2 X3)))) X1 X2 X3
       have r₂ := eq12 (M.op X2 (M.op X1 (M.op X2 X3))) X1
       grind)
    | (have r₁ := eq31 X0 X1 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq166 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X1 X3 x X3
       have i₂ := eq20 X3 X1 (M.op X1 x) X0 X2
       grind)
    | (have i₁ := eq21 X1 X3 x X3
       have i₂ := eq20 X0 X1 X2 X3 (M.op X1 x)
       grind)
    | exact superpose eq20 eq21
    | exact resolve eq21 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq287 : ∀ X0 X1 X2 X3 X5 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X2)))) = X5 ∨ (k X5 X3) = (M.op X5 X3) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq38 X5 X3 X1 (M.op X3 x)
       have i₂ := eq20 X3 X1 x X0 X2
       grind)
    | (have i₁ := eq38 X5 X3 X1 (M.op X3 x)
       have i₂ := eq20 X0 X1 X2 X3 x
       grind)
    | exact superpose eq20 eq38
    | (have j0 := eq38 X5 X0 X1 (M.op X0 X2)
       grind)
    | exact resolve eq38 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq322 : ∀ X1 X3 X5 : G, (M.op X1 X1) = X5 ∨ (k X5 X3) = (M.op X5 X3) := by
    intro X1 X3 X5
    first
    | (have i₁ := eq287 x X1 x X3 X5
       have i₂ := eq166 x X1 x X1
       grind)
    | exact superpose eq166 eq287
    | (have j0 := eq287 x X1 x X3 X5
       grind)
    | exact resolve eq287 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq287
  have eq491 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X2 X1 (M.op X2 x)
       have i₂ := eq38 X0 X1 X2 x
       grind)
    | (have i₁ := eq26 X0 X1 X2
       have i₂ := eq38 (M.op X0 (M.op X1 X2)) X1 X2 x
       grind)
    | exact superpose eq38 eq26
    | (have j1 := eq38 X0 X2 X2 x
       grind)
    | (have r₁ := eq26 X2 X1 (M.op X2 x)
       have r₂ := eq38 (M.op X2 X2) X1 X2 x
       grind)
    | exact resolve eq26 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq38
  have eq505 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq491 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq510 : ∀ X0 X2 : G, (M.op X0 X2) = (k X0 X2) := by
    intro X0 X2
    first
    | (have j0 := eq505 X0 x X2
       have j1 := eq322 x X2 X0
       grind)
    | (have r₁ := eq505 x x X2
       have r₂ := eq322 x x x
       grind)
    | (have r₁ := eq505 (M.op x x) x X2
       have r₂ := eq322 x x (M.op x x)
       grind)
    | (have r₁ := eq505 (k x x) x X2
       have r₂ := eq322 x x x
       grind)
    | exact resolve eq505 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq505
  have eq674 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq510 (σ X0) (σ X1)
       grind)
    | exact superpose eq510 eq15
    | exact resolve eq15 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq674 X0 X1
       have i₂ := eq510 X0 X1
       grind)
    | exact superpose eq510 eq674
    | exact resolve eq674 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq674
  have eq682 : False := by grind
  exact eq682

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pxy_y_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
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
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
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
  have eq77 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (M.op X3 X3) = X1 ∨ (k X1 X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X1 X3
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X3
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq94 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
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
  clear eq67
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
  have eq1016 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X4 X4) = X1 ∨ (k X1 X4) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq77 X0 X1 (M.op x (M.op X1 (M.op x x))) X4
       have i₂ := eq54 x X1 x X0
       grind)
    | exact superpose eq54 eq77
    | (have j0 := eq77 X0 X1 x X4
       grind)
    | exact resolve eq77 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq77
  have eq1041 : ∀ X0 X1 X4 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X4 X4) = X1 ∨ (k X1 X4) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq1016 X0 X1 X4
       have i₂ := eq241 X0 X0
       grind)
    | exact superpose eq241 eq1016
    | (have j0 := eq1016 X0 X1 X4
       grind)
    | (have r₁ := eq1016 X0 (M.op X0 X0) X4
       have r₂ := eq241 X0 X0
       grind)
    | exact resolve eq1016 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq1370 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f1370_15 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
      intro X0 X1
      grind
    have f1370_17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
      intro X0 X1
      grind
    have f1370_18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
      intro X0 X1
      grind
    have f1370_20 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
      intro X0 X1
      grind
    have f1370_24 : (M.op X0 (M.op X0 X0)) ≠ (σ (k X1 X1)) := by grind
    have f1370_26 : (M.op X0 (M.op X0 X0)) ≠ (σ X1) := by grind
    have f1370_31 : ∀ X0 : G, (M.op X0 X0) ≠ (σ X1) := by
      intro X0
      first
      | (have i₁ := f1370_26
         have i₂ := f1370_15 X0 X0
         grind)
      | exact superpose f1370_15 f1370_26
      | exact resolve f1370_26 f1370_15
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1370_55 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (k X1 X1)) := by
      intro X0
      first
      | (have i₁ := f1370_24
         have i₂ := f1370_15 X0 X0
         grind)
      | exact superpose f1370_15 f1370_24
      | exact resolve f1370_24 f1370_15
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1370_207 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
      intro X0 X1
      grind
    have f1370_221 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
      intro X0 X1
      first
      | (have j0 := f1370_207 X0 X1
         grind)
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1370_845 : ∀ X0 X1 : G, (σ X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
      intro X0 X1
      first
      | (have i₁ := f1370_31 X0
         have i₂ := f1370_221 X0 X1
         grind)
      | exact superpose f1370_221 f1370_31
      | (have j1 := f1370_221 X0 X1
         grind)
      | (have r₁ := f1370_31 (σ X1)
         have r₂ := f1370_221 (σ X1) X1
         grind)
      | exact resolve f1370_31 f1370_221
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1370_2107 : ∀ X0 : G, (k (σ X1) X0) = (M.op (σ X1) X0) := by
      intro X0
      first
      | (have j0 := f1370_845 (σ X1) X0
         grind)
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1370_2224 : ∀ X0 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
      intro X0
      first
      | (have i₁ := f1370_17 X1 X0
         have i₂ := f1370_2107 (σ X0)
         grind)
      | exact superpose f1370_2107 f1370_17
      | exact resolve f1370_17 f1370_2107
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1370_2377 : (σ (k X1 X1)) ≠ (σ (k X1 X1)) := by
      first
      | (have i₁ := f1370_55 (σ X1)
         have i₂ := f1370_2224 X1
         grind)
      | exact superpose f1370_2224 f1370_55
      | (have r₁ := f1370_55 (σ X1)
         have r₂ := f1370_2224 X1
         grind)
      | exact resolve f1370_55 f1370_2224
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1370_2397 : False := by grind
    exact f1370_2397
  have eq1386 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 (σ X0)
       have i₂ := eq93 X0 X0
       grind)
    | exact superpose eq93 eq56
    | (have j1 := eq93 X0 X0
       grind)
    | exact resolve eq56 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1404 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq93 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1405 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1404 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq1415 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1386 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq1431 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1370 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq1437 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1415 X0 X1
       have i₂ := eq241 X1 X1
       grind)
    | exact superpose eq241 eq1415
    | (have j0 := eq1415 X0 X1
       grind)
    | exact resolve eq1415 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415
  have eq1440 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1431 X0 X1
       have i₂ := eq241 X0 X0
       grind)
    | exact superpose eq241 eq1431
    | (have j0 := eq1431 X0 X1
       grind)
    | exact resolve eq1431 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431
  have eq1469 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1440 X0 X1
       have i₂ := eq241 X0 X0
       grind)
    | exact superpose eq241 eq1440
    | (have j0 := eq1440 X0 X1
       grind)
    | exact resolve eq1440 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq1440
  have eq1470 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq5614 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1469 X0 (τ X1)
       grind)
    | exact superpose eq1469 eq35
    | (have j1 := eq1469 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5615 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq1469 X0 x
       grind)
    | exact superpose eq1469 eq44
    | (have j1 := eq1469 X0 x
       grind)
    | exact resolve eq44 eq1469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq5643 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq5615 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5615
    | (have j0 := eq5615 X0
       grind)
    | exact resolve eq5615 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5615
  have eq5644 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5614 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5614
    | (have j0 := eq5614 X0 X1
       grind)
    | exact resolve eq5614 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5614
  have eq5704 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5644 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5644
    | (have j0 := eq5644 X0 X1
       grind)
    | exact resolve eq5644 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5644
  have eq8026 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq233 X0 X1
       have i₂ := eq5643 X0
       grind)
    | exact superpose eq5643 eq233
    | (have j1 := eq5643 X1
       grind)
    | exact resolve eq233 eq5643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5643
  have eq8347 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5704 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5704
  have eq8458 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8347 X1 (τ X0)
       have i₂ := eq1470 X0 X0
       grind)
    | exact superpose eq1470 eq8347
    | (have j0 := eq8347 X1 (τ X0)
       grind)
    | exact resolve eq8347 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq10729 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1405 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq1405
    | (have j0 := eq1405 (τ X0)
       grind)
    | exact resolve eq1405 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq10737 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10729 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10729
    | (have j0 := eq10729 X0
       grind)
    | exact resolve eq10729 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10729
  have eq10746 : ∀ X0 : G, (σ (τ X0)) = (M.op x (M.op (σ (τ X0)) (M.op x y))) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq10737 X0
       have i₂ := eq52 (σ (τ X0))
       grind)
    | exact superpose eq52 eq10737
    | (have j0 := eq10737 X0
       grind)
    | exact resolve eq10737 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10737
  have eq10751 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op x (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10746 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10746
    | (have j0 := eq10746 X0
       grind)
    | exact resolve eq10746 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10746
  have eq10846 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq1437 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1437
    | (have j0 := eq1437 x X0
       grind)
    | exact resolve eq1437 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437
  have eq10953 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10846 X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10846
    | exact resolve eq10846 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq10846
  have eq11676 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op x (M.op (σ x) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq10953 eq10751
    | (have j0 := eq10751 (σ x)
       grind)
    | exact resolve eq10751 eq10953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10751 eq10953
  have eq11687 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq52 eq11676
    | (have j0 := eq11676 X0
       grind)
    | exact resolve eq11676 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq11676
  have eq11688 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq11687 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11687
  have eq13084 : ∀ X0 X1 : G, (k x x) = (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq8026 eq50
    | (have j1 := eq8026 X1 X1
       grind)
    | exact resolve eq50 eq8026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq8026
  have eq20545 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq94 X0
       grind)
    | (have r₁ := eq94 X0
       have r₂ := eq11688 (σ x)
       grind)
    | (have r₁ := eq94 X0
       have r₂ := eq11688 (σ X0)
       grind)
    | exact resolve eq94 eq11688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq20634 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20545 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20545
    | (have j0 := eq20545 y
       grind)
    | exact resolve eq20545 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20545
  have eq20653 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20634
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq20634
    | exact resolve eq20634 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20634
  have eq20673 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq20653
    | exact resolve eq20653 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20653
  have eq43708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq113 eq20673
    | exact resolve eq20673 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq20673
  have eq43719 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq43708
       have r₂ := eq28
       grind)
    | exact resolve eq43708 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43708
  have eq43782 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq43719 eq13084
    | (have j0 := eq13084 X0 X0
       grind)
    | exact resolve eq13084 eq43719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13084 eq43719
  have eq43807 : ∀ X0 : G, x = (k x x) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq43782
    | (have j0 := eq43782 X0
       grind)
    | exact resolve eq43782 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43782
  have eq43816 : ∀ X0 : G, x = (k x x) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq43807 X0
       have j1 := eq1041 X0 x x
       grind)
    | (have r₁ := eq43807 X0
       have r₂ := eq1041 X0 (σ x) x
       grind)
    | (have r₁ := eq43807 X0
       have r₂ := eq1041 x x x
       grind)
    | (have r₁ := eq43807 X0
       have r₂ := eq1041 y x x
       grind)
    | exact resolve eq43807 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041 eq43807
  have eq43817 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq43816 X0
       have j1 := eq8347 x x
       grind)
    | (have r₁ := eq43816 X0
       have r₂ := eq8347 X0 x
       grind)
    | exact resolve eq43816 eq8347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8347 eq43816
  have eq43821 : ∀ X0 : G, (k x x) = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    grind
  have eq44851 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1405 x
       have i₂ := eq43821 X0
       grind)
    | exact superpose eq43821 eq1405
    | (have j0 := eq1405 x
       have j1 := eq43821 (σ x)
       grind)
    | exact resolve eq1405 eq43821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405 eq43821
  have eq44892 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44851 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44851
    | (have j0 := eq44851 (σ x)
       grind)
    | exact resolve eq44851 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44851
  have eq44911 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44892 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44892
    | (have j0 := eq44892 (σ x)
       grind)
    | exact resolve eq44892 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44892
  have eq44921 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq44911 (σ x)
       grind)
    | (have r₁ := eq44911 x
       have r₂ := eq11688 (σ x)
       grind)
    | (have r₁ := eq44911 x
       have r₂ := eq11688 x
       grind)
    | exact resolve eq44911 eq11688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44911
  have eq45507 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44921
       have i₂ := eq43817 X0
       grind)
    | exact superpose eq43817 eq44921
    | (have j1 := eq43817 (σ x)
       grind)
    | exact resolve eq44921 eq43817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43817 eq44921
  have eq45524 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq45507 (σ x)
       grind)
    | (have r₁ := eq45507 x
       have r₂ := eq11688 (σ x)
       grind)
    | (have r₁ := eq45507 x
       have r₂ := eq11688 x
       grind)
    | exact resolve eq45507 eq11688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11688 eq45507
  have eq45526 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq45524
       have r₂ := eq23
       grind)
    | exact resolve eq45524 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq45524
  have eq45527 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq45526
       have i₂ := eq233 sF2 x
       grind)
    | (have i₁ := eq45526
       have i₂ := eq233 X0 sF2
       grind)
    | exact superpose eq233 eq45526
    | exact resolve eq45526 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq45530 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by grind
  have eq45547 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq45526 eq977
    | exact resolve eq977 eq45526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq45604 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq45526 eq45530
    | exact resolve eq45530 eq45526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45526 eq45530
  have eq46109 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | exact superpose eq45604 eq8458
    | (have j0 := eq8458 (σ x) X0
       grind)
    | exact resolve eq8458 eq45604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8458 eq45604
  have eq46128 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | (have j0 := eq46109 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46109
  have eq46149 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq29 eq46128
    | exact resolve eq46128 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq46128
  have eq46170 : x = (σ x) := by
    first
    | (have i₁ := eq46149 x
       have i₂ := eq45527 x
       grind)
    | exact superpose eq45527 eq46149
    | exact resolve eq46149 eq45527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45527 eq46149
  have eq46174 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq46170 eq27
    | exact resolve eq27 eq46170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq46841 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq46170 eq45547
    | exact resolve eq45547 eq46170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45547
  have eq46916 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq46841 y
       grind)
    | exact superpose eq46841 eq45
    | exact resolve eq45 eq46841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq46952 : (σ (M.op x y)) = (k x (σ y)) := by
    first
    | exact superpose eq46170 eq46916
    | exact resolve eq46916 eq46170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46170 eq46916
  have eq47028 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq46952
       have i₂ := eq46841 sF3
       grind)
    | exact superpose eq46841 eq46952
    | exact resolve eq46952 eq46841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46841 eq46952
  have eq47100 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46174 eq47028
    | exact resolve eq47028 eq46174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46174 eq47028
  have eq47147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq47100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47100
    | exact resolve eq47100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq47100
  have eq47180 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq47147
    | exact resolve eq47147 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq47147
  have eq47200 : False := by grind
  exact eq47200

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_pyy_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  clear eq23
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
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq51 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X1 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X1 X3 X4
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
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
  have eq55 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
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
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X2))) X1) = (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X1) := by
    intro X0 X1 X2
    grind
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq105 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 (M.op x (M.op X0 (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq404 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 X1 X2
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X2)))) = (M.op X3 (M.op X4 (M.op X3 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq51 X3 X4 X5 X1 (M.op X4 x)
       have i₂ := eq51 X4 X1 x X0 X2
       grind)
    | (have i₁ := eq51 X3 X4 X5 X1 (M.op X4 x)
       have i₂ := eq51 X0 X1 X2 X4 x
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq530 : ∀ X0 X3 X4 X5 : G, (M.op X0 X0) = (M.op X3 (M.op X4 (M.op X3 X5))) := by
    intro X0 X3 X4 X5
    first
    | (have i₁ := eq502 X0 x x X3 X4 X5
       have i₂ := eq14 X0 x (M.op X0 x)
       grind)
    | exact superpose eq14 eq502
    | exact resolve eq502 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq954 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
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
  have eq980 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq954 X0 X1
       have i₂ := eq241 X0 X0
       grind)
    | exact superpose eq241 eq954
    | exact resolve eq954 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq1299 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
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
  have eq1315 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq1332 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1333 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1332 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332
  have eq1343 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1315 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1359 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1299 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq1365 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1343 X0 X1
       have i₂ := eq241 X1 X1
       grind)
    | exact superpose eq241 eq1343
    | (have j0 := eq1343 X0 X1
       grind)
    | exact resolve eq1343 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343
  have eq1367 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1359 X0 X1
       have i₂ := eq241 X0 X0
       grind)
    | exact superpose eq241 eq1359
    | (have j0 := eq1359 X0 X1
       grind)
    | exact resolve eq1359 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359
  have eq1383 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1367 X0 X1
       have i₂ := eq241 X0 X0
       grind)
    | exact superpose eq241 eq1367
    | (have j0 := eq1367 X0 X1
       grind)
    | exact resolve eq1367 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq1367
  have eq1943 : ∀ X0 X1 : G, (k (M.op x (M.op X0 (M.op x y))) X1) = (M.op (M.op x (M.op X0 (M.op x y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq980 X0 X1
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq980
    | exact resolve eq980 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2153 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq211 X0 (M.op x (M.op X0 sF0))
       have i₂ := eq530 (M.op x (M.op X0 sF0)) X3 x x
       grind)
    | exact superpose eq530 eq211
    | exact resolve eq211 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq530
  have eq2259 : ∀ X1 X3 : G, (M.op x (M.op X1 (M.op x y))) = (M.op X3 (M.op x (M.op X1 (M.op x y)))) := by
    intro X1 X3
    first
    | (have i₁ := eq2153 x X1 x X3
       have i₂ := eq207 x X1 x
       grind)
    | (have i₁ := eq2153 x X1 y X3
       have i₂ := eq207 x X1 x
       grind)
    | exact superpose eq207 eq2153
    | (have j0 := eq2153 x X1 y X3
       grind)
    | exact resolve eq2153 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq2153
  have eq5688 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1383 X0 (τ X1)
       grind)
    | exact superpose eq1383 eq35
    | (have j1 := eq1383 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383
  have eq5717 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5688 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5688
    | (have j0 := eq5688 X0 X1
       grind)
    | exact resolve eq5688 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5688
  have eq5776 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5717 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5717
    | (have j0 := eq5717 X0 X1
       grind)
    | exact resolve eq5717 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5717
  have eq8419 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5776 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10390 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1333 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq1333
    | (have j0 := eq1333 (τ X0)
       grind)
    | exact resolve eq1333 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1333
  have eq10398 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10390 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10390
    | (have j0 := eq10390 X0
       grind)
    | exact resolve eq10390 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10390
  have eq10407 : ∀ X0 : G, (σ (τ X0)) = (M.op x (M.op (σ (τ X0)) (M.op x y))) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq10398 X0
       have i₂ := eq52 (σ (τ X0))
       grind)
    | exact superpose eq52 eq10398
    | (have j0 := eq10398 X0
       grind)
    | exact resolve eq10398 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10398
  have eq10412 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op x (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10407 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10407
    | (have j0 := eq10407 X0
       grind)
    | exact resolve eq10407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10407
  have eq10624 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq1365 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1365
    | (have j0 := eq1365 y X0
       grind)
    | exact resolve eq1365 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10702 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1365 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq10728 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10624 X0
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq10624
    | exact resolve eq10624 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq10624
  have eq11186 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (M.op x (M.op (σ y) (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq10728 eq10412
    | (have j0 := eq10412 (σ y)
       grind)
    | exact resolve eq10412 eq10728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10412 eq10728
  have eq11197 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq52 eq11186
    | (have j0 := eq11186 X0
       grind)
    | exact resolve eq11186 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11186
  have eq11198 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq11197 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11197
  have eq43772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq43779 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq43772
    | exact resolve eq43772 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43772
  have eq43790 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq43779
       have r₂ := eq28
       grind)
    | exact resolve eq43779 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43779
  have eq43792 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 X0) = (σ x) ∨ (M.op X0 X0) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq43790
       have i₂ := eq233 sF3 x
       grind)
    | (have i₁ := eq43790
       have i₂ := eq233 X0 sF3
       grind)
    | exact superpose eq233 eq43790
    | exact resolve eq43790 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43790
  have eq43880 : ∀ X0 X1 : G, (M.op X1 X1) = (σ y) ∨ (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = y ∨ (M.op X0 X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq43792 X0
       have i₂ := eq233 y X1
       grind)
    | (have i₁ := eq43792 X0
       have i₂ := eq233 X0 y
       grind)
    | exact superpose eq233 eq43792
    | (have j0 := eq43792 X1
       grind)
    | exact resolve eq43792 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43792
  have eq44418 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = y ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq53 sF4
       have i₂ := eq43880 X0 sF4
       grind)
    | (have i₁ := eq53 sF4
       have i₂ := eq43880 sF4 x
       grind)
    | exact superpose eq43880 eq53
    | (have j1 := eq43880 X0 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq53 eq43880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43880
  have eq44450 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = y ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq27 eq44418
    | (have j0 := eq44418 X0
       grind)
    | exact resolve eq44418 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44418
  have eq44599 : ∀ X0 X1 : G, (M.op X1 X1) = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have i₁ := eq44450 X0
       have i₂ := eq233 sF4 X1
       grind)
    | (have i₁ := eq44450 X0
       have i₂ := eq233 X0 sF4
       grind)
    | exact superpose eq233 eq44450
    | (have j0 := eq44450 X1
       grind)
    | exact resolve eq44450 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44450
  have eq44933 : ∀ X0 : G, y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 sF0
       have i₂ := eq44599 X0 sF0
       grind)
    | exact superpose eq44599 eq52
    | (have j1 := eq44599 X0 (M.op x y)
       grind)
    | exact resolve eq52 eq44599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44599
  have eq45007 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq44933 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq44933
    | (have j0 := eq44933 X0
       grind)
    | exact resolve eq44933 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44933
  have eq45147 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = x ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq45007 X0
       have i₂ := eq233 sF0 X1
       grind)
    | (have i₁ := eq45007 X0
       have i₂ := eq233 X0 sF0
       grind)
    | exact superpose eq233 eq45007
    | (have j0 := eq45007 X1
       grind)
    | exact resolve eq45007 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45183 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op X2 X2) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq404 X0 X1 X2
       have i₂ := eq45007 X0
       grind)
    | exact superpose eq45007 eq404
    | (have j1 := eq45007 X2
       grind)
    | exact resolve eq404 eq45007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq45193 : ∀ X0 X1 : G, (k x X0) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X1 X1) = (σ x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq980 X0 X1
       have i₂ := eq45007 X0
       grind)
    | exact superpose eq45007 eq980
    | (have j1 := eq45007 X1
       grind)
    | exact resolve eq980 eq45007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45007
  have eq48493 : ∀ X0 X1 : G, (σ x) ≠ (M.op X1 x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq45183 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45183
  have eq48616 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X1 X1) = (σ x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq48493 X1 x
       have i₂ := eq233 x X0
       grind)
    | (have i₁ := eq48493 X1 x
       have i₂ := eq233 X0 x
       grind)
    | exact superpose eq233 eq48493
    | (have j0 := eq48493 X1 X1
       grind)
    | exact resolve eq48493 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48493
  have eq48980 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq45
       have i₂ := eq45193 y X0
       grind)
    | exact superpose eq45193 eq45
    | (have j1 := eq45193 X0 X0
       grind)
    | exact resolve eq45 eq45193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq45193
  have eq49012 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq48980 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48980
    | (have j0 := eq48980 X0
       grind)
    | exact resolve eq48980 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48980
  have eq49052 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21 eq49012
    | (have j0 := eq49012 X0
       grind)
    | exact resolve eq49012 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49012
  have eq49090 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq49052 eq11
    | (have j0 := eq11 (σ y) (σ y)
       have j1 := eq49052 (σ y)
       grind)
    | exact resolve eq11 eq49052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49052
  have eq49097 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq49090 (σ y)
       have j1 := eq48616 x (σ y)
       grind)
    | (have r₁ := eq49090 x
       have r₂ := eq48616 (σ y) x
       grind)
    | (have r₁ := eq49090 x
       have r₂ := eq48616 x x
       grind)
    | exact resolve eq49090 eq48616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48616 eq49090
  have eq49108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq49097
    | exact resolve eq49097 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49097
  have eq49110 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq49108
       have r₂ := eq28
       grind)
    | exact resolve eq49108 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49108
  have eq49530 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (M.op X0 X0) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq49110
       have i₂ := eq233 sF3 x
       grind)
    | (have i₁ := eq49110
       have i₂ := eq233 X0 sF3
       grind)
    | exact superpose eq233 eq49110
    | exact resolve eq49110 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49110
  have eq50284 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53 sF4
       have i₂ := eq49530 sF4
       grind)
    | exact superpose eq49530 eq53
    | (have j1 := eq49530 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq53 eq49530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49530
  have eq50357 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq50284
    | exact resolve eq50284 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50284
  have eq50358 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq50357
  have eq50550 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq50358 eq980
    | exact resolve eq980 eq50358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980 eq50358
  have eq53449 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq50550 eq50
    | exact resolve eq50 eq50550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq53466 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq50550 eq61
    | exact resolve eq61 eq50550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq50550
  have eq53488 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq53466
    | exact resolve eq53466 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53466
  have eq55996 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = x ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53449
       have i₂ := eq45147 X0 sF2
       grind)
    | (have i₁ := eq53449
       have i₂ := eq45147 sF2 x
       grind)
    | exact superpose eq45147 eq53449
    | (have j1 := eq45147 X0 x
       grind)
    | exact resolve eq53449 eq45147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45147 eq53449
  have eq56079 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq55996 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55996
  have eq56123 : ∀ X0 : G, x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq29 eq56079
    | (have j0 := eq56079 X0
       grind)
    | exact resolve eq56079 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq56079
  have eq56133 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq56123 X0
       have j1 := eq8419 X0 x
       grind)
    | (have r₁ := eq56123 X0
       have r₂ := eq8419 X0 x
       grind)
    | exact resolve eq56123 eq8419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8419 eq56123
  have eq56346 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    grind
  clear eq56133
  have eq61310 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53488
       have i₂ := eq56346 y
       grind)
    | exact superpose eq56346 eq53488
    | exact resolve eq53488 eq56346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53488 eq56346
  have eq61322 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq61310
  have eq61341 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq61322
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61322
    | exact resolve eq61322 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61322
  have eq61404 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61341 eq15
    | exact resolve eq15 eq61341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61341
  have eq61465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq61404
    | exact resolve eq61404 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61404
  have eq61466 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq61465
       have r₂ := eq28
       grind)
    | exact resolve eq61465 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61465
  have eq61469 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq61466 eq53
    | exact resolve eq53 eq61466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq61576 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq61469
    | (have j0 := eq61469 (σ x)
       grind)
    | exact resolve eq61469 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61469
  have eq61939 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61466 eq61576
    | exact resolve eq61576 eq61466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61576
  have eq61959 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq61939
  have eq61961 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq61959
    | exact resolve eq61959 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61959
  have eq61975 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61961
       have i₂ := eq233 sF2 x
       grind)
    | (have i₁ := eq61961
       have i₂ := eq233 X0 sF2
       grind)
    | exact superpose eq233 eq61961
    | exact resolve eq61961 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62046 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61961 eq11198
    | exact resolve eq11198 eq61961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11198 eq61961
  have eq62149 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq62046
       have r₂ := eq61466
       grind)
    | exact resolve eq62046 eq61466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61466 eq62046
  have eq62156 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X0 (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61975 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq61975
    | exact resolve eq61975 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62322 : ∀ X1 : G, (M.op (σ x) (σ y)) = (k X1 X1) ∨ (M.op (σ x) (σ y)) = X1 ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq5776 x X1
       have i₂ := eq61975 x
       grind)
    | exact superpose eq61975 eq5776
    | exact resolve eq5776 eq61975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61975
  have eq62678 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq62149
       have i₂ := eq233 sF3 x
       grind)
    | (have i₁ := eq62149
       have i₂ := eq233 X0 sF3
       grind)
    | exact superpose eq233 eq62149
    | exact resolve eq62149 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62697 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq62149
  have eq63215 : ∀ X1 : G, (σ y) = (k X1 X1) ∨ (σ y) = X1 ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq5776 x X1
       have i₂ := eq62678 x
       grind)
    | exact superpose eq62678 eq5776
    | exact resolve eq5776 eq62678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5776
  have eq66054 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq62156 sF0
       have i₂ := eq62678 sF0
       grind)
    | exact superpose eq62678 eq62156
    | exact resolve eq62156 eq62678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62156
  have eq66161 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ y = (M.op x y) := by grind
  clear eq66054
  have eq67178 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq62697 eq105
    | exact resolve eq105 eq62697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq62697
  have eq87486 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq67178
       have i₂ := eq62678 sF3
       grind)
    | exact superpose eq62678 eq67178
    | exact resolve eq67178 eq62678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62678 eq67178
  have eq87559 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq87486
  have eq87615 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq87559
    | exact resolve eq87559 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq87559
  have eq87667 : y = (M.op (σ x) (σ y)) ∨ y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq62322 y
       have i₂ := eq87615
       grind)
    | exact superpose eq87615 eq62322
    | (have j0 := eq62322 y
       grind)
    | exact resolve eq62322 eq87615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62322
  have eq87668 : y = (σ y) ∨ y = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq63215 y
       have i₂ := eq87615
       grind)
    | exact superpose eq87615 eq63215
    | (have j0 := eq63215 y
       grind)
    | exact resolve eq63215 eq87615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63215 eq87615
  have eq87683 : y = (σ y) ∨ y = (M.op x y) := by grind
  clear eq87668
  have eq87684 : y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq87667
  have eq87848 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq87683 eq66161
    | exact resolve eq66161 eq87683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66161 eq87683
  have eq87877 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq87848
  have eq87909 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq87877
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87877
    | exact resolve eq87877 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87877
  have eq88033 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq87909 eq87684
    | exact resolve eq87684 eq87909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87684 eq87909
  have eq88034 : y = (M.op x y) := by grind
  clear eq88033
  have eq88069 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq88034 eq21
    | exact resolve eq21 eq88034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88071 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq88034 eq52
    | exact resolve eq52 eq88034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq88226 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq88069
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq88069
    | exact resolve eq88069 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq88069
  have eq88230 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq88226 eq27
    | exact resolve eq27 eq88226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq88226
  have eq88585 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq88071 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88071
    | (have j0 := eq88071 x
       grind)
    | exact resolve eq88071 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88071
  have eq88974 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq88034 eq88585
    | exact resolve eq88585 eq88034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88585
  have eq89048 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq88974
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88974
    | exact resolve eq88974 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88974
  have eq89072 : y = (M.op x x) := by
    first
    | exact superpose eq88034 eq89048
    | exact resolve eq89048 eq88034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89048
  have eq89080 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq89072
       have i₂ := eq233 x X0
       grind)
    | (have i₁ := eq89072
       have i₂ := eq233 X0 x
       grind)
    | exact superpose eq233 eq89072
    | exact resolve eq89072 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq89072
  have eq89560 : ∀ X1 : G, y = (M.op X1 y) := by
    intro X1
    first
    | (have i₁ := eq55 x (M.op x x) x
       have i₂ := eq89080 (M.op x x)
       grind)
    | exact superpose eq89080 eq55
    | exact resolve eq55 eq89080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq91121 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ y = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10702 X0
       have i₂ := eq89080 (σ X0)
       grind)
    | exact superpose eq89080 eq10702
    | (have j0 := eq10702 X0
       grind)
    | exact resolve eq10702 eq89080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10702 eq89080
  have eq91341 : ∀ X0 : G, (σ (M.op x (M.op X0 (M.op x y)))) ≠ (σ (M.op (M.op x (M.op X0 (M.op x y))) (M.op x (M.op X0 (M.op x y))))) ∨ y = (σ (M.op (M.op x (M.op X0 (M.op x y))) (M.op x (M.op X0 (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq1943 eq91121
    | exact resolve eq91121 eq1943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943 eq91121
  have eq91431 : ∀ X0 : G, (σ (M.op x (M.op X0 (M.op x y)))) ≠ (σ (M.op x (M.op X0 (M.op x y)))) ∨ y = (σ (M.op (M.op x (M.op X0 (M.op x y))) (M.op x (M.op X0 (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq2259 eq91341
    | (have j0 := eq91341 X0
       grind)
    | exact resolve eq91341 eq2259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91341
  have eq91432 : ∀ X0 : G, y = (σ (M.op (M.op x (M.op X0 (M.op x y))) (M.op x (M.op X0 (M.op x y))))) := by
    intro X0
    first
    | (have j0 := eq91431 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91431
  have eq91465 : ∀ X0 : G, y = (σ (M.op x (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq2259 eq91432
    | exact resolve eq91432 eq2259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259 eq91432
  have eq91494 : ∀ X0 : G, y = (σ (M.op x (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq88034 eq91465
    | exact resolve eq91465 eq88034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88034 eq91465
  have eq91519 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq91494 x
       have i₂ := eq89560 x
       grind)
    | exact superpose eq89560 eq91494
    | exact resolve eq91494 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91494
  have eq91543 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq91519
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq91519
    | exact resolve eq91519 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq91519
  have eq91567 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq91543
    | exact resolve eq91543 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq91543
  have eq91704 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq91567 eq88230
    | exact resolve eq88230 eq91567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88230
  have eq91706 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq91704
       have i₂ := eq89560 sF2
       grind)
    | exact superpose eq89560 eq91704
    | exact resolve eq91704 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89560 eq91704
  have eq91915 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq91706 eq28
    | exact resolve eq28 eq91706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq91706
  have eq91964 : False := by grind
  exact eq91964

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_pyx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  clear eq23
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
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
  have eq55 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
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
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (M.op X3 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X3 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq105 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq243 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
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
  have eq402 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq55
  have eq623 : ∀ X0 : G, (M.op x x) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq402 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq13 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq638 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq623 X0
       grind)
    | (have r₁ := eq623 X0
       have r₂ := eq235 x (M.op x y)
       grind)
    | (have r₁ := eq623 X0
       have r₂ := eq235 (M.op x y) x
       grind)
    | exact resolve eq623 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq659 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq403 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq13 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq674 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq659 X0
       grind)
    | (have r₁ := eq659 X0
       have r₂ := eq235 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq659 X0
       have r₂ := eq235 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq659 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq954 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X4 X4) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq67 X0 X1 (M.op x (M.op X1 (M.op x x))) X4
       have i₂ := eq54 x X1 x X0
       grind)
    | exact superpose eq54 eq67
    | (have j0 := eq67 X0 X1 x X4
       grind)
    | exact resolve eq67 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq67
  have eq979 : ∀ X0 X1 X4 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X4 X4) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq954 X0 X1 X4
       have i₂ := eq243 X0 X0
       grind)
    | exact superpose eq243 eq954
    | (have j0 := eq954 X0 X1 X4
       grind)
    | (have r₁ := eq954 X0 (M.op X0 X0) X4
       have r₂ := eq243 X0 X0
       grind)
    | exact resolve eq954 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq1298 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
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
  clear eq56
  have eq1305 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq77 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1308 : ∀ X0 : G, (M.op x (M.op (σ X0) (M.op x y))) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq52
    | (have j1 := eq77 X0 X0
       grind)
    | exact resolve eq52 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1348 : ∀ X0 : G, (M.op x (M.op (σ X0) (M.op x y))) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1308 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308
  have eq1351 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1305 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1358 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1366 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1351 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq1351 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq1351 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351
  have eq1367 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1358 X0 X1
       have i₂ := eq243 X0 X0
       grind)
    | exact superpose eq243 eq1358
    | (have j0 := eq1358 X0 X1
       grind)
    | exact resolve eq1358 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq1397 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1367 X0 X1
       have i₂ := eq243 X0 X0
       grind)
    | exact superpose eq243 eq1367
    | (have j0 := eq1367 X0 X1
       grind)
    | exact resolve eq1367 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq1367
  have eq1647 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq638 X1
       have i₂ := eq235 X1 X0
       grind)
    | (have i₁ := eq638 X1
       have i₂ := eq235 X0 X1
       grind)
    | exact superpose eq235 eq638
    | exact resolve eq638 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq1713 : ∀ X0 : G, (M.op x (M.op X0 (M.op x y))) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq674 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq674
    | exact resolve eq674 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1718 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq674 X1
       have i₂ := eq235 X1 X0
       grind)
    | (have i₁ := eq674 X1
       have i₂ := eq235 X0 X1
       grind)
    | exact superpose eq235 eq674
    | exact resolve eq674 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2040 : ∀ X0 X1 : G, (k X1 (σ (M.op (M.op x y) (M.op x y)))) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq1647 eq35
    | exact resolve eq35 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq2131 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq1718 eq35
    | exact resolve eq35 eq1718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq7363 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1397 X0 (τ X1)
       grind)
    | exact superpose eq1397 eq35
    | (have j1 := eq1397 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1397
  have eq7393 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7363 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7363
    | (have j0 := eq7363 X0 X1
       grind)
    | exact resolve eq7363 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7363
  have eq7471 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7393 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7393
    | (have j0 := eq7393 X0 X1
       grind)
    | exact resolve eq7393 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7393
  have eq8288 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | exact superpose eq2040 eq2040
    | exact resolve eq2040 eq2040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq10826 : ∀ X0 : G, (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ≠ (σ (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq674 eq1366
    | (have j0 := eq1366 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0
       grind)
    | exact resolve eq1366 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366
  have eq10851 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have j0 := eq10826 X0
       grind)
    | (have r₁ := eq10826 X0
       have r₂ := eq8288 (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq10826 X0
       have r₂ := eq8288 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq10826 eq8288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8288 eq10826
  have eq10882 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq10851 X1
       have i₂ := eq235 X1 X0
       grind)
    | (have i₁ := eq10851 X1
       have i₂ := eq235 X0 X1
       grind)
    | exact superpose eq235 eq10851
    | exact resolve eq10851 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10922 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq2131 eq10851
    | exact resolve eq10851 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131
  have eq11046 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq10851 eq38
    | exact resolve eq38 eq10851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq11047 : (M.op (σ x) (σ x)) = (σ (k x (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq10851 eq36
    | exact resolve eq36 eq10851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq11048 : (M.op (σ y) (σ y)) = (σ (k y (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq10851 eq37
    | exact resolve eq37 eq10851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq10851
  have eq11075 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq674 eq11048
    | exact resolve eq11048 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11048
  have eq11076 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq674 eq11047
    | exact resolve eq11047 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11047
  have eq11077 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq674 eq11046
    | exact resolve eq11046 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq11046
  have eq11168 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq11075
       grind)
    | exact superpose eq11075 eq16
    | exact resolve eq16 eq11075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11075
  have eq11216 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq11076
       grind)
    | exact superpose eq11076 eq16
    | exact resolve eq16 eq11076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11076
  have eq11486 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 x) X1 x
       have i₂ := eq10922 X0 (M.op X1 x)
       grind)
    | exact superpose eq10922 eq14
    | exact resolve eq14 eq10922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10922
  have eq14527 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq10882 eq10
    | exact resolve eq10 eq10882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10882
  have eq14560 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1713 eq14527
    | exact resolve eq14527 eq1713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713 eq14527
  have eq19409 : (σ (k y y)) = (M.op x (M.op (σ y) (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1348 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1348
    | (have j0 := eq1348 y
       grind)
    | exact resolve eq1348 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348
  have eq19533 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq52 eq19409
    | exact resolve eq19409 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq19409
  have eq19555 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19533
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq19533
    | exact resolve eq19533 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq19533
  have eq19564 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq979 x (σ y) (σ y)
       grind)
    | (have r₁ := eq19555
       have r₂ := eq979 (σ y) (k (σ y) (σ y)) x
       grind)
    | (have r₁ := eq19555
       have r₂ := eq979 (σ y) (σ y) x
       grind)
    | exact resolve eq19555 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979 eq19555
  have eq19575 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq19564 eq105
    | exact resolve eq105 eq19564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq19580 : (k y y) = (M.op y y) := by
    first
    | exact superpose eq11168 eq19575
    | exact resolve eq19575 eq11168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11168 eq19575
  have eq51605 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7471 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7471
  have eq51850 : ∀ X0 : G, y ≠ (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq51605 X0 y
       have i₂ := eq19580
       grind)
    | exact superpose eq19580 eq51605
    | (have j0 := eq51605 X0 y
       grind)
    | exact resolve eq51605 eq19580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19580
  have eq51854 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq19564 eq51605
    | (have j0 := eq51605 X0 (σ y)
       grind)
    | exact resolve eq51605 eq19564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19564 eq51605
  have eq51858 : ∀ X0 X1 : G, (M.op X0 X0) ≠ y ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq51850 X1
       have i₂ := eq235 y X0
       grind)
    | (have i₁ := eq51850 X1
       have i₂ := eq235 X0 y
       grind)
    | exact superpose eq235 eq51850
    | (have j0 := eq51850 X1
       grind)
    | exact resolve eq51850 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51850
  have eq51866 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ y) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq51854 X0
       have i₂ := eq235 sF3 X1
       grind)
    | (have i₁ := eq51854 X0
       have i₂ := eq235 X0 sF3
       grind)
    | exact superpose eq235 eq51854
    | (have j0 := eq51854 X1
       grind)
    | exact resolve eq51854 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51854
  have eq80138 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq51858 x x
       grind)
    | (have r₁ := eq93
       have r₂ := eq51858 x x
       grind)
    | (have r₁ := eq93
       have r₂ := eq51858 y x
       grind)
    | exact resolve eq93 eq51858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq51858
  have eq80143 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq80138 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq80138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80138
  have eq80156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq51866 x (σ x)
       grind)
    | (have r₁ := eq80143
       have r₂ := eq51866 (σ x) x
       grind)
    | (have r₁ := eq80143
       have r₂ := eq51866 (σ y) x
       grind)
    | exact resolve eq80143 eq51866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51866 eq80143
  have eq80161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq80156
    | exact resolve eq80156 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80156
  have eq80163 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq80161
       have r₂ := eq28
       grind)
    | exact resolve eq80161 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80161
  have eq80169 : (τ (σ y)) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq80163 eq11216
    | exact resolve eq11216 eq80163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11216 eq80163
  have eq80329 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq80169
    | exact resolve eq80169 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq80169
  have eq80330 : y = (M.op x x) := by grind
  clear eq80329
  have eq80339 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq80330
       have i₂ := eq235 x X0
       grind)
    | (have i₁ := eq80330
       have i₂ := eq235 X0 x
       grind)
    | exact superpose eq235 eq80330
    | exact resolve eq80330 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq80388 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11486 x x
       have i₂ := eq80330
       grind)
    | exact superpose eq80330 eq11486
    | exact resolve eq11486 eq80330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11486 eq80330
  have eq80491 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq80388 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq80388
    | (have j0 := eq80388 X0
       grind)
    | exact resolve eq80388 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80388
  have eq80921 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14560 X0 sF0
       have i₂ := eq80339 sF0
       grind)
    | exact superpose eq80339 eq14560
    | exact resolve eq14560 eq80339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14560
  have eq80956 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq11077
       have i₂ := eq80339 sF0
       grind)
    | exact superpose eq80339 eq11077
    | exact resolve eq11077 eq80339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11077
  have eq81011 : y = (σ y) := by
    first
    | (have i₁ := eq80956
       have i₂ := eq80339 sF1
       grind)
    | exact superpose eq80339 eq80956
    | exact resolve eq80956 eq80339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80956
  have eq81042 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq80921 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80921
    | (have j0 := eq80921 X0
       grind)
    | exact resolve eq80921 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq80921
  have eq81371 : y = (σ y) := by
    first
    | (have i₁ := eq81011
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq81011
    | exact resolve eq81011 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq81011
  have eq81394 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq81042
    | (have j0 := eq81042 X0
       grind)
    | exact resolve eq81042 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq81042
  have eq81550 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq81394 x
       have i₂ := eq80339 x
       grind)
    | exact superpose eq80339 eq81394
    | exact resolve eq81394 eq80339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80339 eq81394
  have eq81849 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq81371 eq27
    | exact resolve eq27 eq81371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq82196 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq81371 eq80491
    | exact resolve eq80491 eq81371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80491 eq81371
  have eq88362 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81849
       have i₂ := eq82196 sF2
       grind)
    | exact superpose eq82196 eq81849
    | exact resolve eq81849 eq82196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81849 eq82196
  have eq88363 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq88362 eq28
    | exact resolve eq28 eq88362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq88362
  have eq88380 : False := by grind
  exact eq88380

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_y_pyy_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
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
  clear eq23
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
  have eq60 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X1 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X1 X3 X4
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
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
  have eq64 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
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
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (k X3 X1) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X3 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq253 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65 x X0
       have i₂ := eq65 x X1
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq65 X1 X0
       grind)
    | exact superpose eq65 eq14
    | exact resolve eq14 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq430 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 X1 X2
       have i₂ := eq65 X1 X0
       grind)
    | exact superpose eq65 eq64
    | exact resolve eq64 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X1 X1)
       have i₂ := eq430 X1 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq430 X0 X1 X2
       grind)
    | exact superpose eq430 eq13
    | (have j0 := eq13 X2 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X2 (M.op X0 X0))
       have r₂ := eq430 X0 (M.op X2 (M.op X0 X0)) X2
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq430 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq660 : ∀ X1 X2 : G, (M.op X1 X1) = (k X2 (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq642 x X1 X2
       grind)
    | (have r₁ := eq642 x X1 X2
       have r₂ := eq253 x X1
       grind)
    | (have r₁ := eq642 X1 x X2
       have r₂ := eq253 x X1
       grind)
    | exact resolve eq642 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq642
  have eq769 : ∀ X0 X1 X2 X3 X5 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X2)))) ≠ X3 ∨ (k X5 X3) = X3 := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq67 X1 X3 (M.op X3 x) X5
       have i₂ := eq60 X3 X1 x X0 X2
       grind)
    | (have i₁ := eq67 X1 X3 (M.op X3 x) X5
       have i₂ := eq60 X0 X1 X2 X3 x
       grind)
    | exact superpose eq60 eq67
    | (have j0 := eq67 X0 X3 X2 X5
       grind)
    | exact resolve eq67 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq67
  have eq777 : ∀ X0 X3 X5 : G, (M.op X0 X0) ≠ X3 ∨ (k X5 X3) = X3 := by
    intro X0 X3 X5
    first
    | (have i₁ := eq769 X0 x x X3 X5
       have i₂ := eq14 X0 x (M.op X0 x)
       grind)
    | exact superpose eq14 eq769
    | (have j0 := eq769 X0 x x X3 X5
       grind)
    | (have r₁ := eq769 X0 x x (M.op X0 X0) X5
       have r₂ := eq14 X0 x (M.op X0 x)
       grind)
    | exact resolve eq769 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq1251 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X0
       have i₂ := eq65 X0 (σ X0)
       grind)
    | exact superpose eq65 eq77
    | exact resolve eq77 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1267 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq65
    | (have j1 := eq77 X0 X0
       grind)
    | exact resolve eq65 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1285 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1286 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1285 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1297 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq1313 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1251 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1320 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1297 X0 X1
       have i₂ := eq262 X1 X1
       grind)
    | exact superpose eq262 eq1297
    | (have j0 := eq1297 X0 X1
       grind)
    | exact resolve eq1297 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq1323 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1313 X0 X1
       have i₂ := eq262 X0 X0
       grind)
    | exact superpose eq262 eq1313
    | (have j0 := eq1313 X0 X1
       grind)
    | exact resolve eq1313 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq1353 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1323 X0 X1
       have i₂ := eq262 X0 X0
       grind)
    | exact superpose eq262 eq1323
    | (have j0 := eq1323 X0 X1
       grind)
    | exact resolve eq1323 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1537 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (M.op X0 X0)
       have i₂ := eq660 X0 (τ X1)
       grind)
    | exact superpose eq660 eq35
    | exact resolve eq35 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1656 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq398 X1 (M.op X0 X0)
       have i₂ := eq660 X0 (σ X1)
       grind)
    | exact superpose eq660 eq398
    | exact resolve eq398 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq7521 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1353 X1 (M.op X0 X0)
       have i₂ := eq660 X0 (M.op X0 X0)
       grind)
    | exact superpose eq660 eq1353
    | (have j0 := eq1353 X1 (M.op X0 X0)
       grind)
    | exact resolve eq1353 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq7523 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1353 X1 (σ (M.op X0 X0))
       have i₂ := eq1537 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq1537 eq1353
    | (have j0 := eq1353 X1 (σ (M.op X0 X0))
       grind)
    | exact resolve eq1353 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537
  have eq7617 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1353 X0 (τ X1)
       grind)
    | exact superpose eq1353 eq35
    | (have j1 := eq1353 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1353
  have eq7637 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq7523 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7523
  have eq7638 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7521 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7521
  have eq7650 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7617 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7617
    | (have j0 := eq7617 X0 X1
       grind)
    | exact resolve eq7617 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7617
  have eq7717 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7650 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7650
    | (have j0 := eq7650 X0 X1
       grind)
    | exact resolve eq7650 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7650
  have eq7750 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7638 X2 X0
       have i₂ := eq262 X1 X0
       grind)
    | (have i₁ := eq7638 X0 (M.op X0 X0)
       have i₂ := eq262 X0 (M.op X0 X0)
       grind)
    | exact superpose eq262 eq7638
    | exact resolve eq7638 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq7776 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op x (M.op X0 (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7638 X0 X1
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq7638
    | exact resolve eq7638 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq7638
  have eq10561 : ∀ X0 X1 X3 : G, (σ (M.op X3 X3)) = (M.op X1 (σ (σ (M.op X0 X0)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq7750 X1 x X3
       have i₂ := eq7637 X0 x
       grind)
    | exact superpose eq7637 eq7750
    | exact resolve eq7750 eq7637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7637 eq7750
  have eq14794 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1286 y
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq1286
    | (have j0 := eq1286 y
       grind)
    | exact resolve eq1286 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq14801 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq14794
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14794
    | exact resolve eq14794 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14794
  have eq14809 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq14801
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14801
    | exact resolve eq14801 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14801
  have eq15041 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq1320 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1320
    | (have j0 := eq1320 y X0
       grind)
    | exact resolve eq1320 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq15204 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15041 X0
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq15041
    | exact resolve eq15041 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq15041
  have eq50869 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7717 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7717
  have eq52025 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq15204 eq14809
    | exact resolve eq14809 eq15204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14809 eq15204
  have eq52054 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq52025 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52025
  have eq126282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq126290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq126282
       have r₂ := eq52054 (σ x)
       grind)
    | (have r₁ := eq126282
       have r₂ := eq52054 (σ y)
       grind)
    | exact resolve eq126282 eq52054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52054 eq126282
  have eq126301 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq126290
    | exact resolve eq126290 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126290
  have eq126303 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq126301
       have r₂ := eq28
       grind)
    | exact resolve eq126301 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126301
  have eq126331 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq126303 eq1656
    | exact resolve eq1656 eq126303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1656 eq126303
  have eq126501 : ∀ X0 : G, y = (k X0 y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq30 eq126331
    | exact resolve eq126331 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq126331
  have eq126503 : ∀ X0 : G, y = (k X0 y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq126501 X0
       have j1 := eq777 X0 y X0
       grind)
    | (have r₁ := eq126501 X0
       have r₂ := eq777 x y x
       grind)
    | (have r₁ := eq126501 X0
       have r₂ := eq777 y y x
       grind)
    | exact resolve eq126501 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq126501
  have eq126504 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq126503 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq126503 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq126503 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126503
  have eq126576 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq50869 X0 y
       have i₂ := eq126504 y
       grind)
    | exact superpose eq126504 eq50869
    | (have j0 := eq50869 X0 y
       grind)
    | (have r₁ := eq50869 X0 y
       have r₂ := eq126504 y
       grind)
    | exact resolve eq50869 eq126504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50869 eq126504
  have eq126603 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq126576 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126576
  have eq127145 : ∀ X1 : G, y = (M.op X1 y) := by
    intro X1
    first
    | (have i₁ := eq64 x (M.op x x) x
       have i₂ := eq126603 (M.op x x)
       grind)
    | exact superpose eq126603 eq64
    | exact resolve eq64 eq126603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq127231 : ∀ X0 : G, y = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10561 x (σ (σ (M.op x x))) X0
       have i₂ := eq126603 (σ (σ (M.op x x)))
       grind)
    | exact superpose eq126603 eq10561
    | exact resolve eq10561 eq126603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10561
  have eq127266 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7776 sF0 x
       have i₂ := eq126603 sF0
       grind)
    | exact superpose eq126603 eq7776
    | exact resolve eq7776 eq126603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7776
  have eq127381 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq127266 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq127266
    | (have j0 := eq127266 X0
       grind)
    | exact resolve eq127266 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq127266
  have eq127412 : y = (σ y) := by
    first
    | (have i₁ := eq127231 x
       have i₂ := eq126603 x
       grind)
    | exact superpose eq126603 eq127231
    | exact resolve eq127231 eq126603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127231
  have eq127822 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq127381
    | (have j0 := eq127381 X0
       grind)
    | exact resolve eq127381 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq127381
  have eq127844 : y = (σ y) := by
    first
    | (have i₁ := eq127412
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq127412
    | exact resolve eq127412 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq127412
  have eq128002 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq127822 x
       have i₂ := eq126603 x
       grind)
    | exact superpose eq126603 eq127822
    | exact resolve eq127822 eq126603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126603 eq127822
  have eq128317 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq127844 eq27
    | exact resolve eq27 eq127844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq127844
  have eq136782 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq128317
       have i₂ := eq127145 sF2
       grind)
    | exact superpose eq127145 eq128317
    | exact resolve eq128317 eq127145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127145 eq128317
  have eq136787 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq136782 eq28
    | exact resolve eq28 eq136782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq136782
  have eq136788 : False := by grind
  exact eq136788

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxx_pyx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq50 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X1 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X1 X3 X4
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
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
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (M.op X3 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X3 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83
    | exact resolve eq83 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq91
    | exact resolve eq91 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq211 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op x (M.op X1 (M.op x y))) := by
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
  have eq241 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x X0
       have i₂ := eq55 x X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
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
  have eq306 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq409 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 X1 X2
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X2)))) = (M.op X3 (M.op X4 (M.op X3 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq50 X3 X4 X5 X1 (M.op X4 x)
       have i₂ := eq50 X4 X1 x X0 X2
       grind)
    | (have i₁ := eq50 X3 X4 X5 X1 (M.op X4 x)
       have i₂ := eq50 X0 X1 X2 X4 x
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq543 : ∀ X0 X3 X4 X5 : G, (M.op X0 X0) = (M.op X3 (M.op X4 (M.op X3 X5))) := by
    intro X0 X3 X4 X5
    first
    | (have i₁ := eq511 X0 x x X3 X4 X5
       have i₂ := eq14 X0 x (M.op X0 x)
       grind)
    | exact superpose eq14 eq511
    | exact resolve eq511 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq634 : ∀ X0 : G, (M.op x x) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq409 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq13 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq649 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq634 X0
       grind)
    | (have r₁ := eq634 X0
       have r₂ := eq241 x (M.op x y)
       grind)
    | (have r₁ := eq634 X0
       have r₂ := eq241 (M.op x y) x
       grind)
    | exact resolve eq634 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq670 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq410 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq13 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq685 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq670 X0
       grind)
    | (have r₁ := eq670 X0
       have r₂ := eq241 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq670 X0
       have r₂ := eq241 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq670 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq911 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X2 X2) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X1 X1)
       have i₂ := eq413 X1 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq413 X0 X1 X2
       grind)
    | exact superpose eq413 eq13
    | (have j0 := eq13 X2 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X2 (M.op X0 X0))
       have r₂ := eq413 X0 (M.op X2 (M.op X0 X0)) X2
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq413 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq931 : ∀ X1 X2 : G, (M.op X2 X2) = (k X2 (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq911 x X1 X2
       grind)
    | (have r₁ := eq911 x X1 X2
       have r₂ := eq241 x X1
       grind)
    | (have r₁ := eq911 X1 x X2
       have r₂ := eq241 x X1
       grind)
    | exact resolve eq911 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq1116 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X4 X4) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq66 X0 X1 (M.op x (M.op X1 (M.op x x))) X4
       have i₂ := eq53 x X1 x X0
       grind)
    | exact superpose eq53 eq66
    | (have j0 := eq66 X0 X1 x X4
       grind)
    | exact resolve eq66 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq66
  have eq1143 : ∀ X0 X1 X4 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X4 X4) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq1116 X0 X1 X4
       have i₂ := eq249 X0 X0
       grind)
    | exact superpose eq249 eq1116
    | (have j0 := eq1116 X0 X1 X4
       grind)
    | (have r₁ := eq1116 X0 (M.op X0 X0) X4
       have r₂ := eq249 X0 X0
       grind)
    | exact resolve eq1116 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1317 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X0
       have i₂ := eq55 X0 (σ X0)
       grind)
    | exact superpose eq55 eq76
    | exact resolve eq76 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1324 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq76 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq76 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1326 : ∀ X0 : G, (M.op x (M.op (σ X0) (M.op x y))) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0)
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq51
    | (have j1 := eq76 X0 X0
       grind)
    | exact resolve eq51 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1367 : ∀ X0 : G, (M.op x (M.op (σ X0) (M.op x y))) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1326 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1369 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1324 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq1376 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1317 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317
  have eq1384 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1369 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq1369 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq1369 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1385 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1376 X0 X1
       have i₂ := eq249 X0 X0
       grind)
    | exact superpose eq249 eq1376
    | (have j0 := eq1376 X0 X1
       grind)
    | exact resolve eq1376 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq1402 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1385 X0 X1
       have i₂ := eq249 X0 X0
       grind)
    | exact superpose eq249 eq1385
    | (have j0 := eq1385 X0 X1
       grind)
    | exact resolve eq1385 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq1553 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (k X0 (k (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq306 X0 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq306
    | exact resolve eq306 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq1669 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq649 X1
       have i₂ := eq241 X1 X0
       grind)
    | (have i₁ := eq649 X1
       have i₂ := eq241 X0 X1
       grind)
    | exact superpose eq241 eq649
    | exact resolve eq649 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq1804 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op x y))) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq931 X1 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq931
    | exact resolve eq931 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq2056 : ∀ X0 X1 : G, (k X1 (σ (M.op (M.op x y) (M.op x y)))) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq1669 eq34
    | exact resolve eq34 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669
  have eq2400 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X4 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq249 X4 X3
       have i₂ := eq543 X3 X0 X1 X2
       grind)
    | exact superpose eq543 eq249
    | exact resolve eq249 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq7695 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1402 X0 (τ X1)
       grind)
    | exact superpose eq1402 eq34
    | (have j1 := eq1402 X0 (τ X1)
       grind)
    | exact resolve eq34 eq1402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1402
  have eq7725 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7695 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7695
    | (have j0 := eq7695 X0 X1
       grind)
    | exact resolve eq7695 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7695
  have eq7803 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7725 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7725
    | (have j0 := eq7725 X0 X1
       grind)
    | exact resolve eq7725 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7725
  have eq8270 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | exact superpose eq2056 eq2056
    | exact resolve eq2056 eq2056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2056
  have eq10804 : ∀ X0 : G, (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ≠ (σ (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq685 eq1384
    | (have j0 := eq1384 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0
       grind)
    | exact resolve eq1384 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq10829 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have j0 := eq10804 X0
       grind)
    | (have r₁ := eq10804 X0
       have r₂ := eq8270 (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq10804 X0
       have r₂ := eq8270 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq10804 eq8270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8270 eq10804
  have eq11025 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq10829 eq37
    | exact resolve eq37 eq10829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq11026 : (M.op (σ x) (σ x)) = (σ (k x (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq10829 eq35
    | exact resolve eq35 eq10829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq11027 : (M.op (σ y) (σ y)) = (σ (k y (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq10829 eq36
    | exact resolve eq36 eq10829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq10829
  have eq11055 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq685 eq11027
    | exact resolve eq11027 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11027
  have eq11056 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq685 eq11026
    | exact resolve eq11026 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11026
  have eq11057 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq685 eq11025
    | exact resolve eq11025 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq11025
  have eq11147 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq11055
       grind)
    | exact superpose eq11055 eq16
    | exact resolve eq16 eq11055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11055
  have eq11194 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq11056
       grind)
    | exact superpose eq11056 eq16
    | exact resolve eq16 eq11056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11056
  have eq11244 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq11057 eq16
    | exact resolve eq16 eq11057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11057
  have eq19380 : (σ (k x x)) = (M.op x (M.op (σ x) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1367 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1367
    | (have j0 := eq1367 x
       grind)
    | exact resolve eq1367 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq19381 : (σ (k y y)) = (M.op x (M.op (σ y) (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1367 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1367
    | (have j0 := eq1367 y
       grind)
    | exact resolve eq1367 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq19507 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq51 eq19381
    | exact resolve eq19381 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19381
  have eq19508 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq51 eq19380
    | exact resolve eq19380 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19380
  have eq19530 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19507
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq19507
    | exact resolve eq19507 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq19507
  have eq19531 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq19508
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq19508
    | exact resolve eq19508 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq19508
  have eq19539 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq1143 x (σ y) (σ y)
       grind)
    | (have r₁ := eq19530
       have r₂ := eq1143 (σ y) (k (σ y) (σ y)) x
       grind)
    | (have r₁ := eq19530
       have r₂ := eq1143 (σ y) (σ y) x
       grind)
    | exact resolve eq19530 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19530
  have eq19540 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq1143 x (σ x) (σ x)
       grind)
    | (have r₁ := eq19531
       have r₂ := eq1143 (σ x) (k (σ x) (σ x)) x
       grind)
    | (have r₁ := eq19531
       have r₂ := eq1143 (σ x) (σ x) x
       grind)
    | exact resolve eq19531 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143 eq19531
  have eq19557 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq19540 eq49
    | exact resolve eq49 eq19540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq19562 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq11194 eq19557
    | exact resolve eq19557 eq11194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11194 eq19557
  have eq55202 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7803 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7803
  have eq55458 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq19539 eq55202
    | (have j0 := eq55202 X0 (σ y)
       grind)
    | exact resolve eq55202 eq19539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19539 eq55202
  have eq55470 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ y) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq55458 X0
       have i₂ := eq241 sF3 X1
       grind)
    | (have i₁ := eq55458 X0
       have i₂ := eq241 X0 sF3
       grind)
    | exact superpose eq241 eq55458
    | (have j0 := eq55458 X1
       grind)
    | exact resolve eq55458 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55458
  have eq60472 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq94 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq60481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq60472
    | exact resolve eq60472 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60472
  have eq60486 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq60481
       have r₂ := eq27
       grind)
    | exact resolve eq60481 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60481
  have eq60488 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq60486
    | exact resolve eq60486 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60486
  have eq60493 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq60488 eq11147
    | exact resolve eq11147 eq60488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11147 eq60488
  have eq60625 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq60493
    | exact resolve eq60493 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60493
  have eq60626 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq60625
  have eq60629 : ∀ X0 : G, (M.op X0 X0) = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq60626
       have i₂ := eq241 y X0
       grind)
    | (have i₁ := eq60626
       have i₂ := eq241 X0 y
       grind)
    | exact superpose eq241 eq60626
    | exact resolve eq60626 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq60626
  have eq61322 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51 sF0
       have i₂ := eq60629 sF0
       grind)
    | exact superpose eq60629 eq51
    | exact resolve eq51 eq60629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60629
  have eq61460 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq61322
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq61322
    | exact resolve eq61322 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61322
  have eq61461 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq61460
  have eq61583 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq61461 eq52
    | exact resolve eq52 eq61461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq63494 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq61583
    | (have j0 := eq61583 (σ x)
       grind)
    | exact resolve eq61583 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61583
  have eq63919 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61461 eq63494
    | exact resolve eq63494 eq61461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63494
  have eq63941 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq63919
  have eq63942 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq63941
    | exact resolve eq63941 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63941
  have eq64028 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq63942 eq55470
    | (have j0 := eq55470 X0 X0
       grind)
    | exact resolve eq55470 eq63942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55470 eq63942
  have eq64061 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq64028 X0
       grind)
    | (have r₁ := eq64028 X0
       have r₂ := eq61461
       grind)
    | exact resolve eq64028 eq61461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61461 eq64028
  have eq65043 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11244
       have i₂ := eq64061 sF1
       grind)
    | exact superpose eq64061 eq11244
    | exact resolve eq11244 eq64061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11244 eq64061
  have eq65083 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq65043
    | exact resolve eq65043 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq65043
  have eq65954 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq65083 eq51
    | exact resolve eq51 eq65083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq65083
  have eq66105 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq65954
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq65954
    | exact resolve eq65954 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65954
  have eq66106 : y = (M.op x y) := by grind
  clear eq66105
  have eq66153 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq66106 eq20
    | exact resolve eq20 eq66106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq66289 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq66153
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq66153
    | exact resolve eq66153 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66153
  have eq66313 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq66289 eq26
    | exact resolve eq26 eq66289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq66428 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (k X0 (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | exact superpose eq19540 eq1553
    | exact resolve eq1553 eq19540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553 eq19540
  have eq66429 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (M.op x (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq66428 X0
       have i₂ := eq1804 X0 sF2
       grind)
    | exact superpose eq1804 eq66428
    | exact resolve eq66428 eq1804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66428
  have eq66430 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (M.op x (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq66106 eq66429
    | exact resolve eq66429 eq66106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66429
  have eq66431 : ∀ X0 : G, (k (τ X0) (M.op x x)) = (τ (M.op x (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq66430 X0
       have i₂ := eq19562
       grind)
    | exact superpose eq19562 eq66430
    | exact resolve eq66430 eq19562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19562 eq66430
  have eq66432 : ∀ X0 : G, (M.op x (M.op (τ X0) (M.op x y))) = (τ (M.op x (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq66431 X0
       have i₂ := eq1804 (τ X0) x
       grind)
    | exact superpose eq1804 eq66431
    | exact resolve eq66431 eq1804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804 eq66431
  have eq66433 : ∀ X0 : G, (τ (M.op x (M.op X0 y))) = (M.op x (M.op (τ X0) y)) := by
    intro X0
    first
    | exact superpose eq66106 eq66432
    | exact resolve eq66432 eq66106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66432
  have eq66482 : (τ (M.op x (M.op (σ x) y))) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq28 eq66433
    | exact resolve eq66433 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq66433
  have eq66527 : (M.op x (M.op x y)) = (τ (M.op x (M.op (σ x) y))) := by
    first
    | (have i₁ := eq66482
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq66482
    | exact resolve eq66482 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66482
  have eq66569 : (M.op x y) = (τ (M.op x (M.op (σ x) y))) := by
    first
    | exact superpose eq66106 eq66527
    | exact resolve eq66527 eq66106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66527
  have eq66587 : (M.op x y) = (τ (M.op x (M.op (σ x) y))) := by
    first
    | (have i₁ := eq66569
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq66569
    | exact resolve eq66569 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq66569
  have eq66594 : y = (τ (M.op x (M.op (σ x) y))) := by
    first
    | exact superpose eq66106 eq66587
    | exact resolve eq66587 eq66106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66587
  have eq66599 : (σ y) = (M.op x (M.op (σ x) y)) := by
    first
    | exact superpose eq66594 eq15
    | exact resolve eq15 eq66594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66594
  have eq66644 : (σ y) = (M.op x (M.op (σ x) y)) := by
    first
    | (have i₁ := eq66599
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq66599
    | exact resolve eq66599 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq66599
  have eq66653 : (σ (M.op x y)) = (M.op x (M.op (σ x) y)) := by
    first
    | exact superpose eq66289 eq66644
    | exact resolve eq66644 eq66289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66289 eq66644
  have eq66663 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq66653 eq543
    | exact resolve eq543 eq66653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq66696 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq66313 eq66663
    | exact resolve eq66663 eq66313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66313 eq66663
  have eq67024 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op (σ x) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq54 x (M.op x x) x
       have i₂ := eq66696 (M.op x x)
       grind)
    | exact superpose eq66696 eq54
    | exact resolve eq54 eq66696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq70548 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op (σ x) (σ y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2400 X0 X1 X2 X3 x
       have i₂ := eq66696 x
       grind)
    | exact superpose eq66696 eq2400
    | exact resolve eq2400 eq66696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2400 eq66696
  have eq70549 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq67024 eq70548
    | exact resolve eq70548 eq67024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67024 eq70548
  have eq70550 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X1 (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq70549 x X1 x
       have i₂ := eq211 x X1 x
       grind)
    | (have i₁ := eq70549 x X1 y
       have i₂ := eq211 x X1 x
       grind)
    | exact superpose eq211 eq70549
    | (have j0 := eq70549 x X1 y
       grind)
    | exact resolve eq70549 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq70549
  have eq70551 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X1 y)) := by
    intro X1
    first
    | exact superpose eq66106 eq70550
    | exact resolve eq70550 eq66106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66106 eq70550
  have eq70578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66653
       have i₂ := eq70551 sF2
       grind)
    | exact superpose eq70551 eq66653
    | exact resolve eq66653 eq70551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66653 eq70551
  have eq70684 : False := by grind
  exact eq70684
