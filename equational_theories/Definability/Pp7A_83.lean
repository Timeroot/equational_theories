import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pxy_pxx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq14 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ y) (σ x)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq65 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X1) X0 X1
       have i₂ := eq52 (M.op X1 X1) X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq52 X0 (M.op X0 X0)
       grind)
    | exact superpose eq52 eq66
    | exact resolve eq66 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq81
    | exact resolve eq81 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq692 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq70 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq693 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq692 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq3087 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq693 (M.op X0 X0)
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq693
    | (have j0 := eq693 (M.op X0 X0)
       grind)
    | exact resolve eq693 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq3095 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq3087 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3087
  have eq16761 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 (σ (M.op X0 X0))
       have i₂ := eq3095 X0
       grind)
    | exact superpose eq3095 eq65
    | exact resolve eq65 eq3095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3095
  have eq17478 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq82 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq17479 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17478
    | exact resolve eq17478 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17478
  have eq17490 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17479
       have r₂ := eq28
       grind)
    | exact resolve eq17479 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17479
  have eq17495 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq17490 eq52
    | exact resolve eq52 eq17490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17507 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17490 eq56
    | exact resolve eq56 eq17490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17490
  have eq17510 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17507
    | exact resolve eq17507 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17507
  have eq17515 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17510 eq56
    | exact resolve eq56 eq17510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17510
  have eq17524 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq17515 eq65
    | exact resolve eq65 eq17515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17515
  have eq19300 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17524 eq27
    | (have j1 := eq17524 (σ y)
       grind)
    | exact resolve eq27 eq17524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17524
  have eq19324 : x = (M.op y y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19300
  have eq19336 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16761 y x
       have i₂ := eq19324
       grind)
    | exact superpose eq19324 eq16761
    | exact resolve eq16761 eq19324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19324
  have eq19348 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19336 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19336
    | (have j0 := eq19336 X0
       grind)
    | exact resolve eq19336 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19336
  have eq19541 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19348 eq27
    | (have j1 := eq19348 (σ y)
       grind)
    | exact resolve eq27 eq19348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19348
  have eq19567 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19541
  have eq19606 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq19567
       grind)
    | exact superpose eq19567 eq56
    | exact resolve eq56 eq19567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19615 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq52 x X0
       have i₂ := eq19606
       grind)
    | exact superpose eq19606 eq52
    | exact resolve eq52 eq19606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq19622 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16761 x x
       have i₂ := eq19606
       grind)
    | exact superpose eq19606 eq16761
    | exact resolve eq16761 eq19606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16761 eq19606
  have eq19633 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19622 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19622
    | (have j0 := eq19622 X0
       grind)
    | exact resolve eq19622 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19622
  have eq19694 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19567
       have i₂ := eq19615 y
       grind)
    | exact superpose eq19615 eq19567
    | exact resolve eq19567 eq19615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19567 eq19615
  have eq19702 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq19694
  have eq19717 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq19702 eq28
    | exact resolve eq28 eq19702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19702
  have eq19890 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19633 eq27
    | (have j1 := eq19633 (σ y)
       grind)
    | exact resolve eq27 eq19633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq19633
  have eq19922 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19890
  have eq19924 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq19922 eq28
    | exact resolve eq28 eq19922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq19925 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq19922 eq54
    | exact resolve eq54 eq19922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq19922
  have eq29635 : ∀ X0 : G, x = (M.op y y) ∨ (M.op X0 (σ x)) = X0 ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq19925 eq17495
    | (have j0 := eq17495 X0
       grind)
    | exact resolve eq17495 eq19925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17495
  have eq29911 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 (σ x)) = X0 ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq56 y y
       have i₂ := eq29635 X0
       grind)
    | exact superpose eq29635 eq56
    | (have j1 := eq29635 X0
       grind)
    | exact resolve eq56 eq29635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29635
  have eq29914 : ∀ X0 : G, x = (M.op y x) ∨ (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq29911 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29911
    | (have j0 := eq29911 X0
       grind)
    | exact resolve eq29911 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29911
  have eq29929 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq56 x y
       have i₂ := eq29914 X0
       grind)
    | exact superpose eq29914 eq56
    | (have j1 := eq29914 X0
       grind)
    | exact resolve eq56 eq29914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq29914
  have eq29939 : ∀ X0 X1 : G, x = (M.op x X0) ∨ (M.op X1 (σ x)) = X1 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 x
       have i₂ := eq29929 X0
       grind)
    | exact superpose eq29929 eq65
    | (have j1 := eq29929 X1
       grind)
    | exact resolve eq65 eq29929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29929
  have eq30262 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq19
       have i₂ := eq29939 y X0
       grind)
    | exact superpose eq29939 eq19
    | (have j1 := eq29939 y X0
       grind)
    | exact resolve eq19 eq29939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29939
  have eq30297 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq30262 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30262
  have eq30594 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30297 eq69
    | exact resolve eq69 eq30297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30297
  have eq30933 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30594 eq50
    | exact resolve eq50 eq30594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30594
  have eq30980 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq30933
    | exact resolve eq30933 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30933
  have eq31284 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq30980
       grind)
    | exact superpose eq30980 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq30980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30980
  have eq31285 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq31284
  have eq31597 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq65 X0 x
       have i₂ := eq31285
       grind)
    | exact superpose eq31285 eq65
    | exact resolve eq65 eq31285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq31285
  have eq32216 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq31597 y
       grind)
    | exact superpose eq31597 eq19
    | (have j1 := eq31597 y
       grind)
    | exact resolve eq19 eq31597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31597
  have eq32249 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq32216
  have eq32261 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32249 eq30
    | exact resolve eq30 eq32249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32249
  have eq32410 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq32261
    | exact resolve eq32261 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32261
  have eq32687 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq32410 eq21
    | exact resolve eq21 eq32410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32410
  have eq32868 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq32687
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32687
    | exact resolve eq32687 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32687
  have eq32869 : x = y := by
    first
    | (have r₁ := eq32868
       have r₂ := eq19717
       grind)
    | exact resolve eq32868 eq19717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19717 eq32868
  have eq32870 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq32869
       grind)
    | exact superpose eq32869 eq19
    | exact resolve eq19 eq32869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq32871 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq32869
       grind)
    | exact superpose eq32869 eq25
    | exact resolve eq25 eq32869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq32869
  have eq33060 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq32871
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32871
    | exact resolve eq32871 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32871
  have eq33143 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq33060 eq19925
    | exact resolve eq19925 eq33060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19925 eq33060
  have eq33311 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq33143 eq69
    | exact resolve eq69 eq33143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq33143
  have eq34551 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq33311 eq50
    | exact resolve eq50 eq33311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq33311
  have eq34602 : x = (k x x) := by
    first
    | exact superpose eq29 eq34551
    | exact resolve eq34551 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq34551
  have eq38201 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq34602
       grind)
    | exact superpose eq34602 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq34602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34602
  have eq38202 : x = (M.op x x) := by grind
  clear eq38201
  have eq38213 : x = (M.op x y) := by
    first
    | (have i₁ := eq38202
       have i₂ := eq32870
       grind)
    | exact superpose eq32870 eq38202
    | exact resolve eq38202 eq32870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32870 eq38202
  have eq38244 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq38213 eq21
    | exact resolve eq21 eq38213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq38213
  have eq38449 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq38244
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38244
    | exact resolve eq38244 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq38244
  have eq38518 : False := by grind
  exact eq38518

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pxy_pyx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq14 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ y) (σ x)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq65 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X1) X0 X1
       have i₂ := eq52 (M.op X1 X1) X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq52 X0 (M.op X0 X0)
       grind)
    | exact superpose eq52 eq66
    | exact resolve eq66 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq81
    | exact resolve eq81 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq690 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq70 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq691 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq690 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq3085 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq691 (M.op X0 X0)
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq691
    | (have j0 := eq691 (M.op X0 X0)
       grind)
    | exact resolve eq691 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq3093 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq3085 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3085
  have eq16699 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 (σ (M.op X0 X0))
       have i₂ := eq3093 X0
       grind)
    | exact superpose eq3093 eq65
    | exact resolve eq65 eq3093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3093
  have eq17337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq82 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq17338 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17337
    | exact resolve eq17337 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17337
  have eq17349 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17338
       have r₂ := eq28
       grind)
    | exact resolve eq17338 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17338
  have eq17354 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq17349 eq52
    | exact resolve eq52 eq17349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17366 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17349 eq56
    | exact resolve eq56 eq17349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17349
  have eq17369 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17366
    | exact resolve eq17366 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17366
  have eq17374 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17369 eq56
    | exact resolve eq56 eq17369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17369
  have eq17385 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq17374 eq65
    | exact resolve eq65 eq17374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17374
  have eq19398 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17385 eq27
    | (have j1 := eq17385 (σ y)
       grind)
    | exact resolve eq27 eq17385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17385
  have eq19430 : x = (M.op y y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19398
  have eq19442 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16699 y x
       have i₂ := eq19430
       grind)
    | exact superpose eq19430 eq16699
    | exact resolve eq16699 eq19430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19430
  have eq19454 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19442 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19442
    | (have j0 := eq19442 X0
       grind)
    | exact resolve eq19442 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19442
  have eq19542 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19454 eq27
    | (have j1 := eq19454 (σ y)
       grind)
    | exact resolve eq27 eq19454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19454
  have eq19574 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19542
  have eq19579 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq19574
       grind)
    | exact superpose eq19574 eq56
    | exact resolve eq56 eq19574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19710 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq52 x X0
       have i₂ := eq19579
       grind)
    | exact superpose eq19579 eq52
    | exact resolve eq52 eq19579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq19717 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16699 x x
       have i₂ := eq19579
       grind)
    | exact superpose eq19579 eq16699
    | exact resolve eq16699 eq19579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16699 eq19579
  have eq19728 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19717 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19717
    | (have j0 := eq19717 X0
       grind)
    | exact resolve eq19717 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19717
  have eq19755 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19574
       have i₂ := eq19710 y
       grind)
    | exact superpose eq19710 eq19574
    | exact resolve eq19574 eq19710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19574 eq19710
  have eq19763 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq19755
  have eq19778 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq19763 eq28
    | exact resolve eq28 eq19763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19763
  have eq20078 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19728 eq27
    | (have j1 := eq19728 (σ y)
       grind)
    | exact resolve eq27 eq19728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq19728
  have eq20110 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20078
  have eq20112 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq20110 eq28
    | exact resolve eq28 eq20110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq20113 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq20110 eq54
    | exact resolve eq54 eq20110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq20110
  have eq33600 : ∀ X0 : G, x = (M.op y y) ∨ (M.op X0 (σ x)) = X0 ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq20113 eq17354
    | (have j0 := eq17354 X0
       grind)
    | exact resolve eq17354 eq20113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17354
  have eq33616 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 (σ x)) = X0 ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq56 y y
       have i₂ := eq33600 X0
       grind)
    | exact superpose eq33600 eq56
    | (have j1 := eq33600 X0
       grind)
    | exact resolve eq56 eq33600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33600
  have eq33619 : ∀ X0 : G, x = (M.op y x) ∨ (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq33616 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq33616
    | (have j0 := eq33616 X0
       grind)
    | exact resolve eq33616 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33616
  have eq33634 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq56 x y
       have i₂ := eq33619 X0
       grind)
    | exact superpose eq33619 eq56
    | (have j1 := eq33619 X0
       grind)
    | exact resolve eq56 eq33619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq33619
  have eq33921 : ∀ X0 X1 : G, x = (M.op x X0) ∨ (M.op X1 (σ x)) = X1 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 x
       have i₂ := eq33634 X0
       grind)
    | exact superpose eq33634 eq65
    | (have j1 := eq33634 X1
       grind)
    | exact resolve eq65 eq33634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33634
  have eq34245 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq19
       have i₂ := eq33921 y X0
       grind)
    | exact superpose eq33921 eq19
    | (have j1 := eq33921 y X0
       grind)
    | exact resolve eq19 eq33921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33921
  have eq34280 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq34245 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34245
  have eq34578 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq34280 eq69
    | exact resolve eq69 eq34280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34280
  have eq34918 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq34578 eq50
    | exact resolve eq50 eq34578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34578
  have eq34962 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq34918
    | exact resolve eq34918 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34918
  have eq35264 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq34962
       grind)
    | exact superpose eq34962 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq34962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34962
  have eq35265 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq35264
  have eq35572 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq65 X0 x
       have i₂ := eq35265
       grind)
    | exact superpose eq35265 eq65
    | exact resolve eq65 eq35265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq35265
  have eq36191 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq35572 y
       grind)
    | exact superpose eq35572 eq19
    | (have j1 := eq35572 y
       grind)
    | exact resolve eq19 eq35572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35572
  have eq36224 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq36191
  have eq36236 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36224 eq30
    | exact resolve eq30 eq36224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq36224
  have eq36394 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq36236
    | exact resolve eq36236 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36236
  have eq36672 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq36394 eq21
    | exact resolve eq21 eq36394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36394
  have eq36871 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq36672
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36672
    | exact resolve eq36672 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36672
  have eq36872 : x = y := by
    first
    | (have r₁ := eq36871
       have r₂ := eq19778
       grind)
    | exact resolve eq36871 eq19778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19778 eq36871
  have eq36873 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq36872
       grind)
    | exact superpose eq36872 eq19
    | exact resolve eq19 eq36872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq36874 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq36872
       grind)
    | exact superpose eq36872 eq25
    | exact resolve eq25 eq36872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq36872
  have eq37079 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq36874
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36874
    | exact resolve eq36874 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36874
  have eq37163 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq37079 eq20113
    | exact resolve eq20113 eq37079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20113 eq37079
  have eq37758 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq37163 eq69
    | exact resolve eq69 eq37163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq37163
  have eq38074 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq37758 eq50
    | exact resolve eq50 eq37758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq37758
  have eq38120 : x = (k x x) := by
    first
    | exact superpose eq29 eq38074
    | exact resolve eq38074 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq38074
  have eq40532 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq38120
       grind)
    | exact superpose eq38120 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq38120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38120
  have eq40533 : x = (M.op x x) := by grind
  clear eq40532
  have eq40542 : x = (M.op x y) := by
    first
    | (have i₁ := eq40533
       have i₂ := eq36873
       grind)
    | exact superpose eq36873 eq40533
    | exact resolve eq40533 eq36873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36873 eq40533
  have eq40571 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq40542 eq21
    | exact resolve eq21 eq40542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq40542
  have eq40792 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40571
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40571
    | exact resolve eq40571 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq40571
  have eq40865 : False := by grind
  exact eq40865

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyy_y_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  clear eq36
  have eq47 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq14 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq47
    | (have j0 := eq47 (σ y) (σ x)
       grind)
    | exact resolve eq47 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (M.op X1 X0) X0
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq47
    | exact resolve eq47 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq50 eq47
    | exact resolve eq47 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq69 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X1) X0 X1
       have i₂ := eq48 (M.op X1 X1) X0
       grind)
    | exact superpose eq48 eq14
    | exact resolve eq14 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq82 : (k x x) = (τ (k (σ x) (σ x))) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq89
    | exact resolve eq89 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq430 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq431 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq430 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq2935 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq431 (M.op X0 X0)
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq431
    | (have j0 := eq431 (M.op X0 X0)
       grind)
    | exact resolve eq431 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq431
  have eq2943 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq2935 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935
  have eq16063 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 (σ (M.op X0 X0))
       have i₂ := eq2943 X0
       grind)
    | exact superpose eq2943 eq69
    | exact resolve eq69 eq2943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2943
  have eq17009 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17009
    | exact resolve eq17009 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17009
  have eq17021 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17010
       have r₂ := eq28
       grind)
    | exact resolve eq17010 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17010
  have eq17025 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  have eq17039 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17021 eq52
    | exact resolve eq52 eq17021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17021
  have eq17042 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17039
    | exact resolve eq17039 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17039
  have eq17046 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17042 eq52
    | exact resolve eq52 eq17042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17042
  have eq17057 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq17046 eq69
    | exact resolve eq69 eq17046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq17046
  have eq19604 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17057 eq27
    | (have j1 := eq17057 (σ y)
       grind)
    | exact resolve eq27 eq17057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17057
  have eq19637 : x = (M.op y y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19604
  have eq19649 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16063 y x
       have i₂ := eq19637
       grind)
    | exact superpose eq19637 eq16063
    | exact resolve eq16063 eq19637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19637
  have eq19662 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19649 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19649
    | (have j0 := eq19649 X0
       grind)
    | exact resolve eq19649 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19649
  have eq20208 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19662 eq27
    | (have j1 := eq19662 (σ y)
       grind)
    | exact resolve eq27 eq19662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19662
  have eq20241 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20208
  have eq20246 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52 x y
       have i₂ := eq20241
       grind)
    | exact superpose eq20241 eq52
    | exact resolve eq52 eq20241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20518 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq48 x X0
       have i₂ := eq20246
       grind)
    | exact superpose eq20246 eq48
    | exact resolve eq48 eq20246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20525 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16063 x x
       have i₂ := eq20246
       grind)
    | exact superpose eq20246 eq16063
    | exact resolve eq16063 eq20246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16063 eq20246
  have eq20537 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq20525 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20525
    | (have j0 := eq20525 X0
       grind)
    | exact resolve eq20525 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20525
  have eq20883 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20241
       have i₂ := eq20518 y
       grind)
    | exact superpose eq20518 eq20241
    | exact resolve eq20241 eq20518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20241 eq20518
  have eq20892 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq20883
  have eq21170 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq20892 eq28
    | exact resolve eq28 eq20892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20892
  have eq21486 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20537 eq27
    | (have j1 := eq20537 (σ y)
       grind)
    | exact resolve eq27 eq20537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20537
  have eq21519 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21486
  have eq21783 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq21519 eq28
    | exact resolve eq28 eq21519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq21784 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq21519 eq50
    | exact resolve eq50 eq21519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq39777 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21784 eq17025
    | exact resolve eq17025 eq21784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17025 eq21784
  have eq39783 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq39777 eq90
    | exact resolve eq90 eq39777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq39777
  have eq39797 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq39783
  have eq39805 : x = (M.op y y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq39797
       have r₂ := eq21783
       grind)
    | exact resolve eq39797 eq21783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39797
  have eq39826 : x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq39805
       grind)
    | exact superpose eq39805 eq52
    | exact resolve eq52 eq39805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39805
  have eq39829 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39826
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq39826
    | exact resolve eq39826 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39826
  have eq39844 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52 x y
       have i₂ := eq39829
       grind)
    | exact superpose eq39829 eq52
    | exact resolve eq52 eq39829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq39855 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq48 x X0
       have i₂ := eq39844
       grind)
    | exact superpose eq39844 eq48
    | exact resolve eq48 eq39844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq39844
  have eq39962 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39829
       have i₂ := eq39855 y
       grind)
    | exact superpose eq39855 eq39829
    | exact resolve eq39829 eq39855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39829 eq39855
  have eq39970 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq39962
  have eq39985 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq39970 eq30
    | exact resolve eq30 eq39970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq39970
  have eq40144 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq39985
    | exact resolve eq39985 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39985
  have eq40145 : x = (M.op x y) ∨ x = y := by grind
  clear eq40144
  have eq40147 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq40145 eq21
    | exact resolve eq21 eq40145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40145
  have eq40362 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq40147
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40147
    | exact resolve eq40147 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40147
  have eq40363 : x = y := by
    first
    | (have r₁ := eq40362
       have r₂ := eq21170
       grind)
    | exact resolve eq40362 eq21170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21170 eq40362
  have eq40365 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq40363
       grind)
    | exact superpose eq40363 eq19
    | exact resolve eq19 eq40363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq40366 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq40363
       grind)
    | exact superpose eq40363 eq25
    | exact resolve eq25 eq40363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq40363
  have eq40586 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq40366
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40366
    | exact resolve eq40366 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40366
  have eq40592 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq40586 eq56
    | exact resolve eq56 eq40586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq40586
  have eq40747 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21519 eq40592
    | exact resolve eq40592 eq21519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21519 eq40592
  have eq40827 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq40747
  have eq41573 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq40827 eq82
    | exact resolve eq82 eq40827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq40827
  have eq41620 : x = (k x x) := by
    first
    | exact superpose eq29 eq41573
    | exact resolve eq41573 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq41573
  have eq43071 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq41620
       grind)
    | exact superpose eq41620 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq41620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41620
  have eq43072 : x = (M.op x x) := by grind
  clear eq43071
  have eq43081 : x = (M.op x y) := by
    first
    | (have i₁ := eq43072
       have i₂ := eq40365
       grind)
    | exact superpose eq40365 eq43072
    | exact resolve eq43072 eq40365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40365 eq43072
  have eq43115 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq43081 eq21
    | exact resolve eq21 eq43081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq43081
  have eq43345 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq43115
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq43115
    | exact resolve eq43115 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq43115
  have eq43423 : False := by grind
  exact eq43423

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxx_x_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq14 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ y) (σ x)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  have eq70 : ∀ X0 X1 : G, (M.op X1 (k (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    grind
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq73 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X1) X0 X1
       have i₂ := eq52 (M.op X1 X1) X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 (M.op X0 (M.op X2 X2))) = (M.op X0 X0) ∨ (M.op X1 (M.op X0 (M.op X2 X2))) = (k (M.op X1 (M.op X0 (M.op X2 X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op X0 (M.op X2 X2))) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 (M.op X0 (M.op X2 X2))) X0
       grind)
    | (have r₁ := eq12 (M.op X1 (M.op X0 (M.op X2 X2))) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 X2))) = (M.op X0 X0) ∨ (M.op X1 (M.op X0 (M.op X2 X2))) = (k (M.op X1 (M.op X0 (M.op X2 X2))) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq79 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq96 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 (M.op X0 (M.op X2 X2))) = (k (M.op X1 (M.op X0 (M.op X2 X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 X0 X1 X2
       have i₂ := eq52 X2 X0
       grind)
    | exact superpose eq52 eq95
    | (have j0 := eq95 X0 X1 X2
       grind)
    | exact resolve eq95 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X1 X1 X0
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq96
    | (have j0 := eq96 X0 X1 x
       grind)
    | exact resolve eq96 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq96
  have eq106 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq111
    | exact resolve eq111 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq114
    | exact resolve eq114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq575 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97 (M.op X1 X0) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq97
    | exact resolve eq97 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq650 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq70 X0 (k (M.op X0 X0) X0)
       grind)
    | exact superpose eq70 eq61
    | exact resolve eq61 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq70
  have eq651 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq650 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq650
    | exact resolve eq650 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq712 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X1) (σ X0)
       have i₂ := eq106 X0 X1
       grind)
    | exact superpose eq106 eq51
    | (have j1 := eq106 X0 X1
       grind)
    | exact resolve eq51 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq106 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq715 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq714 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq2967 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq715 (M.op X0 X0)
       have i₂ := eq651 X0
       grind)
    | exact superpose eq651 eq715
    | (have j0 := eq715 (M.op X0 X0)
       grind)
    | exact resolve eq715 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651 eq715
  have eq2975 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq2967 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2967
  have eq3083 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq71 (M.op X1 X0)
       have i₂ := eq575 X0 X1
       grind)
    | exact superpose eq575 eq71
    | (have j1 := eq575 X0 X1
       grind)
    | exact resolve eq71 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq575
  have eq3091 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3083 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3083
  have eq3101 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3091 (M.op X1 X0) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq3091
    | exact resolve eq3091 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3113 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq54 eq3091
    | exact resolve eq3091 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq3091
  have eq23662 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (σ (M.op X0 X0))
       have i₂ := eq2975 X0
       grind)
    | exact superpose eq2975 eq73
    | exact resolve eq73 eq2975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq2975
  have eq24786 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq24786
    | exact resolve eq24786 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24786
  have eq24798 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq24787
       have r₂ := eq28
       grind)
    | exact resolve eq24787 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24787
  have eq24803 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24798 eq51
    | exact resolve eq51 eq24798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24798
  have eq24812 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq24803
    | exact resolve eq24803 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24803
  have eq24857 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24812 eq56
    | exact resolve eq56 eq24812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24812
  have eq24862 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq24857
    | exact resolve eq24857 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24857
  have eq24863 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq24862
  have eq24880 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3101 x y
       have i₂ := eq24863
       grind)
    | exact superpose eq24863 eq3101
    | exact resolve eq3101 eq24863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3101 eq24863
  have eq27327 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq712 y x
       have i₂ := eq24880
       grind)
    | exact superpose eq24880 eq712
    | (have j0 := eq712 y x
       grind)
    | exact resolve eq712 eq24880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq24880
  have eq27329 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq27327
  have eq27332 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27329
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27329
    | exact resolve eq27329 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27329
  have eq27344 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27332
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27332
    | exact resolve eq27332 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27332
  have eq27349 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq27344
    | exact resolve eq27344 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27344
  have eq27350 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq27349
  have eq27353 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27350
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27350
    | exact resolve eq27350 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27350
  have eq27356 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27353
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27353
    | exact resolve eq27353 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq27353
  have eq27639 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27356 eq51
    | exact resolve eq51 eq27356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27356
  have eq27644 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq27639
    | exact resolve eq27639 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27639
  have eq27645 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27644
  have eq27691 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23662 y x
       have i₂ := eq27645
       grind)
    | exact superpose eq27645 eq23662
    | exact resolve eq23662 eq27645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23662 eq27645
  have eq27711 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq27691 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27691
    | (have j0 := eq27691 X0
       grind)
    | exact resolve eq27691 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27691
  have eq28559 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27711 eq27
    | (have j1 := eq27711 (σ y)
       grind)
    | exact resolve eq27 eq27711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq27711
  have eq28621 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28559
  have eq28635 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq28621 eq28
    | exact resolve eq28 eq28621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq28642 : (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq28621 eq3113
    | exact resolve eq3113 eq28621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3113 eq28621
  have eq28728 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28642 eq115
    | exact resolve eq115 eq28642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq28642
  have eq28750 : y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq28728
       have r₂ := eq28635
       grind)
    | exact resolve eq28728 eq28635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28728
  have eq43591 : x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq51 x y
       have i₂ := eq28750
       grind)
    | exact superpose eq28750 eq51
    | exact resolve eq51 eq28750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq28750
  have eq43600 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43591
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq43591
    | exact resolve eq43591 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43591
  have eq44057 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq43600
       grind)
    | exact superpose eq43600 eq56
    | exact resolve eq56 eq43600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq43600
  have eq44062 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44057
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq44057
    | exact resolve eq44057 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq44057
  have eq44063 : x = (M.op x y) := by grind
  clear eq44062
  have eq44088 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq44063 eq21
    | exact resolve eq21 eq44063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq44063
  have eq44260 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq44088
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44088
    | exact resolve eq44088 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq44088
  have eq44279 : False := by grind
  exact eq44279

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyy_pxx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op X1 X0) X0
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq102 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq118 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq468 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq471 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq102 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq472 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq468 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq468
    | (have j0 := eq468 X0
       grind)
    | exact resolve eq468 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq478 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq472 X0
       have j1 := eq471 X0
       grind)
    | (have r₁ := eq472 X0
       have r₂ := eq471 X0
       grind)
    | exact resolve eq472 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471 eq472
  have eq481 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq478 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq478
    | exact resolve eq478 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66 (σ X0) X1
       have i₂ := eq478 X0
       grind)
    | exact superpose eq478 eq66
    | exact resolve eq66 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq498 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq481 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq481
    | exact resolve eq481 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq481
  have eq499 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq498 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq498
    | exact resolve eq498 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq580 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq488 (M.op X0 X0) X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq488
    | exact resolve eq488 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq488
  have eq619 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65 (σ (M.op X1 X1)) X0
       have i₂ := eq580 X1 X0
       grind)
    | exact superpose eq580 eq65
    | exact resolve eq65 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq580
  have eq705 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq116 x y
       grind)
    | exact superpose eq116 eq16
    | (have j1 := eq116 x y
       grind)
    | exact resolve eq16 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq716 : (σ x) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq705
       have i₂ := eq478 y
       grind)
    | exact superpose eq478 eq705
    | exact resolve eq705 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq725 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq716
       have i₂ := eq499 y
       grind)
    | exact superpose eq499 eq716
    | exact resolve eq716 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq13366 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq118 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq118
    | exact resolve eq118 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq13492 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13366 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13366
    | (have j0 := eq13366 X0 X1
       grind)
    | exact resolve eq13366 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13366
  have eq41228 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq725
       have i₂ := eq13492 x y
       grind)
    | exact superpose eq13492 eq725
    | (have j1 := eq13492 x y
       grind)
    | (have r₁ := eq725
       have r₂ := eq13492 x y
       grind)
    | (have r₁ := eq725
       have r₂ := eq13492 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq725
       have r₂ := eq13492 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq725 eq13492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725 eq13492
  have eq41229 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq41228
  have eq75824 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41229
       grind)
    | exact superpose eq41229 eq16
    | exact resolve eq16 eq41229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41229
  have eq75825 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75824
       have i₂ := eq478 x
       grind)
    | exact superpose eq478 eq75824
    | exact resolve eq75824 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75824
  have eq75826 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75825
       have i₂ := eq499 x
       grind)
    | exact superpose eq499 eq75825
    | exact resolve eq75825 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75825
  have eq75827 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq75826
  have eq75829 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq75827
       grind)
    | exact superpose eq75827 eq10
    | exact resolve eq10 eq75827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75827
  have eq75909 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75829
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq75829
    | exact resolve eq75829 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75829
  have eq75933 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75909
       grind)
    | exact superpose eq75909 eq16
    | exact resolve eq16 eq75909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75909
  have eq75934 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75933
       have i₂ := eq478 x
       grind)
    | exact superpose eq478 eq75933
    | exact resolve eq75933 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq75933
  have eq75935 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75934
       have i₂ := eq499 x
       grind)
    | exact superpose eq499 eq75934
    | exact resolve eq75934 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499 eq75934
  have eq75936 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq75935
  have eq76438 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq75936
       grind)
    | exact superpose eq75936 eq10
    | exact resolve eq10 eq75936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75936
  have eq76522 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq76438
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq76438
    | exact resolve eq76438 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76438
  have eq76523 : x = (M.op y y) := by grind
  clear eq76522
  have eq76540 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq619 X0 y
       have i₂ := eq76523
       grind)
    | exact superpose eq76523 eq619
    | exact resolve eq619 eq76523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq76750 : x = (M.op x y) := by
    first
    | (have i₁ := eq68 y y
       have i₂ := eq76523
       grind)
    | exact superpose eq76523 eq68
    | exact resolve eq68 eq76523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq76523
  have eq78496 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76540 (σ y)
       grind)
    | exact superpose eq76540 eq16
    | exact resolve eq16 eq76540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76540
  have eq78853 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq78496
       have i₂ := eq76750
       grind)
    | exact superpose eq76750 eq78496
    | exact resolve eq78496 eq76750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76750 eq78496
  have eq78854 : False := by grind
  exact eq78854

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxy_pxx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op X1 X1) X0
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq19
    | exact resolve eq19 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq20 X0 (M.op X0 X0)
       grind)
    | exact superpose eq20 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq20 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq32
    | exact resolve eq32 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq32
  have eq59 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq33 X1 (τ X0)
       grind)
    | exact superpose eq33 eq17
    | exact resolve eq17 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 X1))
       have i₂ := eq63 (τ X0) X1
       grind)
    | exact superpose eq63 eq17
    | exact resolve eq17 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq76 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq75
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq83 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq76 (τ X0) X1
       grind)
    | exact superpose eq76 eq17
    | exact resolve eq17 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq84 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq83
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq91 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq109 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 (M.op X1 X1)
       have i₂ := eq33 X1 (σ X0)
       grind)
    | exact superpose eq33 eq91
    | exact resolve eq91 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq122 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq109
    | exact resolve eq109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq130 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq66
    | (have j0 := eq66 X2 X2
       grind)
    | exact resolve eq66 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq66 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq145 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq144 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq219 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op X1 X1))))
       have i₂ := eq84 (τ X0) X1
       grind)
    | exact superpose eq84 eq17
    | exact resolve eq17 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq221 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq219 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq219
    | exact resolve eq219 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq272 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (M.op X1 X1)))))
       have i₂ := eq221 (τ X0) X1
       grind)
    | exact superpose eq221 eq17
    | exact resolve eq17 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq274 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq272
    | exact resolve eq272 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq349 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))
       have i₂ := eq274 (τ X0) X1
       grind)
    | exact superpose eq274 eq17
    | exact resolve eq17 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq353 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq349 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq349
    | exact resolve eq349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq437 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))
       have i₂ := eq353 (τ X0) X1
       grind)
    | exact superpose eq353 eq17
    | exact resolve eq17 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq441 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq437 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq437
    | exact resolve eq437 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq582 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq145 (M.op X0 X0)
       have i₂ := eq33 X0 (M.op X0 X0)
       grind)
    | exact superpose eq33 eq145
    | (have j0 := eq145 (M.op X0 X0)
       grind)
    | exact resolve eq145 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq615 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq582 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq674 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ (M.op X0 X0))
       have i₂ := eq615 X0
       grind)
    | exact superpose eq615 eq30
    | exact resolve eq30 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq2627 : ∀ X0 X1 X2 : G, (k X0 (σ (k (τ X1) X2))) = (M.op (σ (τ X0)) (k X1 (σ X2))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (k (τ X1) X2)
       have i₂ := eq130 X1 X2 (τ X0)
       grind)
    | exact superpose eq130 eq17
    | (have j1 := eq130 X1 X2 (τ X0)
       grind)
    | exact resolve eq17 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq2652 : ∀ X0 X1 X2 : G, (k X0 (σ (k (τ X1) X2))) = (M.op X0 (k X1 (σ X2))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2627 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2627
    | (have j0 := eq2627 X0 X1 X2
       grind)
    | exact resolve eq2627 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2627
  have eq2683 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2652 X0 X1 X2
       have i₂ := eq17 X1 X2
       grind)
    | exact superpose eq17 eq2652
    | (have j0 := eq2652 X0 X1 X2
       grind)
    | exact resolve eq2652 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2652
  have eq2704 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2683 X0 X1 X2
       have j1 := eq12 X0 (k X1 (σ X2))
       grind)
    | (have r₁ := eq2683 X0 X1 X2
       have r₂ := eq12 X0 (σ (τ X0))
       grind)
    | (have r₁ := eq2683 X0 X1 X2
       have r₂ := eq12 X0 (k X1 (σ X2))
       grind)
    | exact resolve eq2683 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683
  have eq2721 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2704 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2704
    | (have j0 := eq2704 X0 X1 X2
       grind)
    | exact resolve eq2704 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2704
  have eq5974 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2721 X0 X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))
       have i₂ := eq441 X0 X1
       grind)
    | exact superpose eq441 eq2721
    | (have j0 := eq2721 X1 X1 x
       grind)
    | exact resolve eq2721 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq2721
  have eq6070 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq5974 X2 X0
       grind)
    | exact superpose eq5974 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq5974 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq5974 X0 X1
       grind)
    | exact resolve eq12 eq5974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6074 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq5974 X2 X0
       grind)
    | exact superpose eq5974 eq33
    | (have j1 := eq5974 X2 X0
       grind)
    | exact resolve eq33 eq5974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq6079 : ∀ X0 X1 X2 : G, (k X1 (τ X0)) = X1 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq122 X1 X0
       have i₂ := eq5974 X2 X0
       grind)
    | exact superpose eq5974 eq122
    | (have j1 := eq5974 X2 X0
       grind)
    | exact resolve eq122 eq5974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq5974
  have eq6114 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6070 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6070
  have eq6445 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq6074 X0 X2 (τ X1)
       grind)
    | exact superpose eq6074 eq18
    | (have j1 := eq6074 X0 X2 X2
       grind)
    | exact resolve eq18 eq6074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq6074
  have eq14585 : ∀ X0 X1 X2 : G, (k (σ X0) X2) = (M.op (σ X0) X2) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6079 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6079
    | (have j0 := eq6079 (σ X0) X1 X2
       grind)
    | exact resolve eq6079 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6079
  have eq44210 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6114 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6114
  have eq44211 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq44210 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44210
  have eq47311 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14585 X0 X2 (σ X1)
       grind)
    | exact superpose eq14585 eq15
    | (have j1 := eq14585 X0 X2 X2
       grind)
    | exact resolve eq15 eq14585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14585
  have eq334005 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6445 X1 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6445
    | (have j0 := eq6445 X1 X1 X2
       grind)
    | exact resolve eq6445 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6445
  have eq334996 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq334005 X0 X1 X2
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq334005
    | (have j0 := eq334005 X0 X1 X2
       grind)
    | exact resolve eq334005 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334005
  have eq380042 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq47311 x y X0
       grind)
    | exact superpose eq47311 eq16
    | (have j1 := eq47311 x x X0
       grind)
    | exact resolve eq16 eq47311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47311
  have eq380465 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq380042 X0
       have j1 := eq334996 X0 x X0
       grind)
    | (have r₁ := eq380042 X0
       have r₂ := eq334996 y x x
       grind)
    | exact resolve eq380042 eq334996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334996 eq380042
  have eq381566 : x = (M.op x x) := by
    first
    | (have i₁ := eq44211 x
       have i₂ := eq380465 x
       grind)
    | exact superpose eq380465 eq44211
    | exact resolve eq44211 eq380465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44211 eq380465
  have eq381931 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq30 X0 x
       have i₂ := eq381566
       grind)
    | exact superpose eq381566 eq30
    | exact resolve eq30 eq381566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq381953 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq674 x x
       have i₂ := eq381566
       grind)
    | exact superpose eq381566 eq674
    | exact resolve eq674 eq381566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq381566
  have eq393599 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq381953 (σ y)
       grind)
    | exact superpose eq381953 eq16
    | exact resolve eq16 eq381953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381953
  have eq393879 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq393599
       have i₂ := eq381931 y
       grind)
    | exact superpose eq381931 eq393599
    | exact resolve eq393599 eq381931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381931 eq393599
  have eq393880 : False := by grind
  exact eq393880

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq20 X0 (M.op X0 X0)
       grind)
    | exact superpose eq20 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq20 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq32
    | exact resolve eq32 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq32
  have eq63 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq33 X1 (τ X0)
       grind)
    | exact superpose eq33 eq17
    | exact resolve eq17 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq67 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63
    | exact resolve eq63 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 X1))
       have i₂ := eq67 (τ X0) X1
       grind)
    | exact superpose eq67 eq17
    | exact resolve eq17 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq80 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq79
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq87 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq80 (τ X0) X1
       grind)
    | exact superpose eq80 eq17
    | exact resolve eq17 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq88 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq131 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq70
    | (have j0 := eq70 X2 X2
       grind)
    | exact resolve eq70 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq234 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op X1 X1))))
       have i₂ := eq88 (τ X0) X1
       grind)
    | exact superpose eq88 eq17
    | exact resolve eq17 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq236 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq234 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq234
    | exact resolve eq234 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq304 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (M.op X1 X1)))))
       have i₂ := eq236 (τ X0) X1
       grind)
    | exact superpose eq236 eq17
    | exact resolve eq17 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq308 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq304
    | exact resolve eq304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq387 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))
       have i₂ := eq308 (τ X0) X1
       grind)
    | exact superpose eq308 eq17
    | exact resolve eq17 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq391 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq387 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq387
    | exact resolve eq387 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq2204 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ X0) (k X1 (σ X2))
       have i₂ := eq131 X1 X2 X0
       grind)
    | exact superpose eq131 eq19
    | (have j1 := eq131 X1 X2 X0
       grind)
    | exact resolve eq19 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq131
  have eq2205 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2204 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204
  have eq15945 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k (k (τ X1) X2) (τ X0))) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2205 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2205
    | exact resolve eq2205 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205
  have eq16039 : ∀ X0 X1 X2 : G, (k (σ (k (τ X1) X2)) X0) = (M.op (k X1 (σ X2)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15945 X0 X1 X2
       have i₂ := eq18 X0 (k (τ X1) X2)
       grind)
    | exact superpose eq18 eq15945
    | (have j0 := eq15945 X0 X1 X2
       grind)
    | exact resolve eq15945 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq15945
  have eq16054 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) X0) = (M.op (k X1 (σ X2)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16039 X0 X1 X2
       have i₂ := eq17 X1 X2
       grind)
    | exact superpose eq17 eq16039
    | (have j0 := eq16039 X0 X1 X2
       grind)
    | exact resolve eq16039 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq16039
  have eq16055 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) X0) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq16054 X0 X1 X2
       have j1 := eq12 (k X1 (σ X2)) X0
       grind)
    | (have r₁ := eq16054 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq16054 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16054
  have eq16086 : ∀ X0 X2 : G, (k X0 X2) = (M.op X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq16055 X0 X0 (σ (σ (σ (σ (σ (M.op x x))))))
       have i₂ := eq391 X0 x
       grind)
    | exact superpose eq391 eq16055
    | exact resolve eq16055 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq16055
  have eq16568 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq16086 (σ X0) (σ X1)
       grind)
    | exact superpose eq16086 eq15
    | exact resolve eq15 eq16086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16649 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16568 X0 X1
       have i₂ := eq16086 X0 X1
       grind)
    | exact superpose eq16086 eq16568
    | exact resolve eq16568 eq16086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16086 eq16568
  have eq19036 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16649 x y
       grind)
    | exact superpose eq16649 eq16
    | (have r₁ := eq16
       have r₂ := eq16649 x y
       grind)
    | exact resolve eq16 eq16649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16649
  have eq19105 : False := by grind
  exact eq19105

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_x_pxx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (M.op X1 X0) X0
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq31
    | exact resolve eq31 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact superpose eq32 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (M.op X1 X1) X0
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq31
    | exact resolve eq31 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq52 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq44 X1 (τ X0)
       grind)
    | exact superpose eq44 eq17
    | exact resolve eq17 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52
    | exact resolve eq52 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq57 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 X1))
       have i₂ := eq53 (τ X0) X1
       grind)
    | exact superpose eq53 eq17
    | exact resolve eq17 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq58 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq91 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq62
    | (have j0 := eq62 X2 X2
       grind)
    | exact resolve eq62 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq62
    | exact resolve eq62 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62 x y
       grind)
    | exact superpose eq62 eq16
    | (have j1 := eq62 x y
       grind)
    | exact resolve eq16 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) X1
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq32
    | (have j1 := eq62 X0 X0
       grind)
    | exact resolve eq32 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq62 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq62 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq62 X0 X1
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq108 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq107 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq110 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq112 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq100 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq117 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq110 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq110 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq127 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq58 (τ X0) X1
       grind)
    | exact superpose eq58 eq17
    | exact resolve eq17 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq130 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq127
    | exact resolve eq127 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq146 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X1)
       have i₂ := eq44 X1 (σ X0)
       grind)
    | exact superpose eq44 eq28
    | exact resolve eq28 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq159 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq146
    | exact resolve eq146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq189 : ∀ X0 X1 : G, (σ (σ (k X0 X0))) ≠ (σ (σ X0)) ∨ (k X1 (σ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq117 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq117
    | (have j0 := eq117 (σ X0) X1
       grind)
    | exact resolve eq117 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, (σ (σ (σ (σ (M.op X0 X0))))) ≠ (σ (σ (σ (σ (M.op X0 X0))))) ∨ (k X1 (σ (σ (σ (σ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq117 (σ (σ (σ (M.op X0 X0)))) X1
       have i₂ := eq130 (σ (σ (σ (M.op X0 X0)))) X0
       grind)
    | exact superpose eq130 eq117
    | (have j0 := eq117 (σ (σ (σ (M.op X0 X0)))) X1
       grind)
    | exact resolve eq117 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq276 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq350 : ∀ X0 X1 : G, (σ (σ (σ (σ (σ (M.op X0 X0)))))) ≠ (σ (σ (σ (σ (σ (M.op X0 X0)))))) ∨ (k X1 (σ (σ (σ (σ (σ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq117 (σ (σ (σ (σ (M.op X0 X0))))) X1
       have i₂ := eq276 X0 (σ (σ (σ (σ (M.op X0 X0)))))
       grind)
    | exact superpose eq276 eq117
    | (have j0 := eq117 (σ (σ (σ (σ (M.op X0 X0))))) X1
       grind)
    | exact resolve eq117 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq356 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq350 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq441 : ∀ X0 X1 : G, (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))) ≠ (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))) ∨ (k X1 (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq117 (σ (σ (σ (σ (σ (M.op X0 X0)))))) X1
       have i₂ := eq356 X0 (σ (σ (σ (σ (σ (M.op X0 X0))))))
       grind)
    | exact superpose eq356 eq117
    | (have j0 := eq117 (σ (σ (σ (σ (σ (M.op X0 X0)))))) X1
       grind)
    | exact resolve eq117 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq441 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq608 : ∀ X0 X1 : G, (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))) ≠ (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))) ∨ (k X1 (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq117 (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))) X1
       have i₂ := eq448 X0 (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))
       grind)
    | exact superpose eq448 eq117
    | (have j0 := eq117 (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))) X1
       grind)
    | exact resolve eq117 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq608 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq636 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq108 (M.op X0 X0)
       have i₂ := eq44 X0 (M.op X0 X0)
       grind)
    | exact superpose eq44 eq108
    | (have j0 := eq108 (M.op X0 X0)
       grind)
    | exact resolve eq108 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq636 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq743 : ∀ X0 X1 X2 : G, (M.op X2 (σ (k X0 X0))) = X2 ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 X0 (σ X0)
       have i₂ := eq112 X0 X1
       grind)
    | exact superpose eq112 eq43
    | (have j1 := eq112 X0 X2
       grind)
    | exact resolve eq43 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq112
  have eq1645 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq96
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq96 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1646 : y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1645
  have eq1781 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ (M.op X0 X0)) X1
       have i₂ := eq663 X0
       grind)
    | exact superpose eq663 eq32
    | exact resolve eq32 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq1823 : ∀ X0 X1 : G, (M.op X1 (σ (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1781 (σ (M.op X0 X0)) X1
       have i₂ := eq1781 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq1781 eq1781
    | exact resolve eq1781 eq1781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1943 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq448 (σ (σ (M.op X0 X0))) X1
       have i₂ := eq1823 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq1823 eq448
    | exact resolve eq448 eq1823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823
  have eq2073 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (σ X0) (k X1 (σ X2))
       have i₂ := eq91 X1 X2 X0
       grind)
    | exact superpose eq91 eq31
    | (have j1 := eq91 X1 X2 X0
       grind)
    | exact resolve eq31 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq2074 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2073 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2073
  have eq2482 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (k X0 (σ X1)) (σ X2)
       have i₂ := eq94 X0 X1 X2
       grind)
    | exact superpose eq94 eq31
    | (have j1 := eq94 X0 X1 X2
       grind)
    | exact resolve eq31 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq2483 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2482 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482
  have eq4475 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq743 X0 (σ (k X0 X0)) (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq4476 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq4475 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4475
  have eq4542 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq4476 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq4476
    | exact resolve eq4476 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4476
  have eq4553 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4542 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4542
    | exact resolve eq4542 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4542
  have eq4608 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq31 (k X0 X0) X0
       have i₂ := eq4553 X0
       grind)
    | exact superpose eq4553 eq31
    | exact resolve eq31 eq4553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4553
  have eq4694 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq4608 (τ X0)
       have i₂ := eq131 X0 X0
       grind)
    | exact superpose eq131 eq4608
    | exact resolve eq4608 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq4608
  have eq17348 : ∀ X0 X1 X2 X3 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (k X2 (σ X3)) (σ X0)) = (σ (k (k (τ X2) X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq159 X1 (σ X0)
       have i₂ := eq2074 X0 X2 X3
       grind)
    | exact superpose eq2074 eq159
    | (have j1 := eq2074 X0 X2 X3
       grind)
    | exact resolve eq159 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq2074
  have eq17399 : ∀ X0 X1 X2 X3 : G, (M.op (k X2 (σ X3)) (σ X0)) = (σ (k (k (τ X2) X3) X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17348 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17348
    | (have j0 := eq17348 X0 X1 X2 X3
       grind)
    | exact resolve eq17348 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17348
  have eq24688 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq31 y x
       have i₂ := eq1646
       grind)
    | exact superpose eq1646 eq31
    | exact resolve eq31 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1646
  have eq24689 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq24688
  have eq28537 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X2) X0) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (M.op X1 X1))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2483 X1 (σ (σ (σ (σ (σ (M.op X0 X0)))))) X2
       have i₂ := eq448 X0 X1
       grind)
    | exact superpose eq448 eq2483
    | exact resolve eq2483 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448 eq2483
  have eq28619 : ∀ X0 X2 : G, (M.op (σ X2) X0) = (σ (k X2 (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq28537 X0 x X2
       have i₂ := eq356 x (τ X0)
       grind)
    | exact superpose eq356 eq28537
    | (have j0 := eq28537 X0 x X2
       grind)
    | exact resolve eq28537 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq28537
  have eq28641 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ (k (σ X2) X0) = (M.op (σ X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq28619 X0 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq28619
    | (have j0 := eq28619 X0 X2
       grind)
    | exact resolve eq28619 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq28619
  have eq33312 : ∀ X0 X1 X2 : G, (k (σ X2) X0) = (M.op (σ X2) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq28641 X0 X2
       grind)
    | exact superpose eq28641 eq44
    | (have j1 := eq28641 X0 X2
       grind)
    | exact resolve eq44 eq28641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq28641
  have eq35890 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33312 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33312
    | (have j0 := eq33312 X1 X2 X2
       grind)
    | exact resolve eq33312 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36197 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) X1) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq33312 X1 (σ X0) x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33312
  have eq36756 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq35890 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35890
  have eq36788 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36756 (M.op X0 X1) X1
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq36756
    | (have j0 := eq36756 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq36756 (M.op X1 X0) X0
       have r₂ := eq34 X0 X1
       grind)
    | exact resolve eq36756 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq36756
  have eq37065 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq36788 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36788
  have eq132855 : ∀ X0 X1 X2 X3 : G, (σ (k (τ X0) X2)) = (M.op (k X0 (σ (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))))) (σ X2)) ∨ (k X3 X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17399 X2 X3 X0 (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1))))))))
       have i₂ := eq617 X1 (τ X0)
       grind)
    | exact superpose eq617 eq17399
    | (have j0 := eq17399 X2 X3 X2 X3
       grind)
    | exact resolve eq17399 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617 eq17399
  have eq133659 : ∀ X0 X2 X3 : G, (σ (k (τ X0) X2)) = (M.op X0 (σ X2)) ∨ (k X3 X2) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq132855 X0 x X2 X3
       have i₂ := eq1943 x X0
       grind)
    | exact superpose eq1943 eq132855
    | (have j0 := eq132855 X0 x X2 X3
       grind)
    | exact resolve eq132855 eq1943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943 eq132855
  have eq133834 : ∀ X0 X2 X3 : G, (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (k X3 X2) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq133659 X0 X2 X3
       have i₂ := eq17 X0 X2
       grind)
    | exact superpose eq17 eq133659
    | (have j0 := eq133659 X0 X2 X3
       grind)
    | exact resolve eq133659 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq133659
  have eq133949 : ∀ X0 X1 X2 : G, (k X2 (τ X0)) = X2 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq133834 X0 (τ X0) x
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq133834
    | (have j0 := eq133834 X0 (τ X0) X2
       grind)
    | exact resolve eq133834 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133834
  have eq134603 : ∀ X0 X1 X2 : G, (σ (σ (τ X0))) ≠ (σ (σ (τ X0))) ∨ (k X1 (σ (σ (τ X0)))) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq189 (τ X0) X1
       have i₂ := eq133949 X0 X2 (τ X0)
       grind)
    | exact superpose eq133949 eq189
    | (have j0 := eq189 (τ X0) X1
       have j1 := eq133949 X0 X2 X2
       grind)
    | exact resolve eq189 eq133949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq133949
  have eq134945 : ∀ X0 X1 X2 : G, (k X1 (σ (σ (τ X0)))) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq134603 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134603
  have eq135106 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134945 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq134945
    | (have j0 := eq134945 X0 X1 X2
       grind)
    | exact resolve eq134945 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134945
  have eq136371 : ∀ X0 X1 X2 : G, (k X2 (τ X0)) = (M.op X2 (τ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135106 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq135106
    | (have j0 := eq135106 (τ X0) X1 X2
       grind)
    | exact resolve eq135106 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135106
  have eq140630 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq108 (τ X0)
       have i₂ := eq136371 X0 X1 (τ X0)
       grind)
    | exact superpose eq136371 eq108
    | (have j0 := eq108 (τ X0)
       have j1 := eq136371 X0 X1 x
       grind)
    | exact resolve eq108 eq136371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq136371
  have eq141042 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq140630 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq140630
    | (have j0 := eq140630 X0 X1
       grind)
    | exact resolve eq140630 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140630
  have eq141071 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141042 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq141042
    | (have j0 := eq141042 X0 X1
       grind)
    | exact resolve eq141042 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141042
  have eq141078 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq141071 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq141071 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq141071 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141071
  have eq141081 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141078 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq141078
    | (have j0 := eq141078 (σ X0) X1
       grind)
    | exact resolve eq141078 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141078
  have eq152381 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq37065 (σ x) (σ y)
       have i₂ := eq24689
       grind)
    | exact superpose eq24689 eq37065
    | exact resolve eq37065 eq24689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24689 eq37065
  have eq152394 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq36197 y (σ y)
       grind)
    | (have r₁ := eq152381
       have r₂ := eq36197 y (σ y)
       grind)
    | exact resolve eq152381 eq36197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36197 eq152381
  have eq152400 : y = (M.op y y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq152394
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq152394
    | exact resolve eq152394 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152394
  have eq152462 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq141081 y X0
       have i₂ := eq152400
       grind)
    | exact superpose eq152400 eq141081
    | (have j0 := eq141081 y X0
       grind)
    | exact resolve eq141081 eq152400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141081 eq152400
  have eq152471 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have j0 := eq152462 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152462
  have eq152475 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq152471 X0
       have j1 := eq117 y X0
       grind)
    | (have r₁ := eq152471 X0
       have r₂ := eq117 y x
       grind)
    | exact resolve eq152471 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq152471
  have eq152623 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq4694 (σ y)
       have i₂ := eq152475 (σ y)
       grind)
    | exact superpose eq152475 eq4694
    | exact resolve eq4694 eq152475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4694 eq152475
  have eq152976 : y = (M.op y y) := by
    first
    | (have i₁ := eq152623
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq152623
    | exact resolve eq152623 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152623
  have eq153289 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq32 y X0
       have i₂ := eq152976
       grind)
    | exact superpose eq152976 eq32
    | exact resolve eq32 eq152976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq153311 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1781 y X0
       have i₂ := eq152976
       grind)
    | exact superpose eq152976 eq1781
    | exact resolve eq1781 eq152976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781 eq152976
  have eq155512 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq153311 (σ x)
       grind)
    | exact superpose eq153311 eq16
    | exact resolve eq16 eq153311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153311
  have eq155528 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq155512
       have i₂ := eq153289 x
       grind)
    | exact superpose eq153289 eq155512
    | exact resolve eq155512 eq153289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153289 eq155512
  have eq155529 : False := by grind
  exact eq155529
