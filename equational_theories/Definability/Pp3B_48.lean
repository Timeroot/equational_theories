import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyy_pyy_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq93 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
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
  have eq403 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq411 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq420 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq403 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq403
    | (have j0 := eq403 X0 X1
       grind)
    | exact resolve eq403 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq802 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq420 x y
       grind)
    | exact superpose eq420 eq16
    | (have j1 := eq420 x y
       grind)
    | exact resolve eq16 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq420 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq2944 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq411 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq411
    | exact resolve eq411 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq2997 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2944 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2944
    | (have j0 := eq2944 X0 X1
       grind)
    | exact resolve eq2944 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2944
  have eq3732 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq802
       have i₂ := eq2997 y x
       grind)
    | exact superpose eq2997 eq802
    | (have j1 := eq2997 (M.op (σ x) (σ y)) (σ (M.op x x))
       grind)
    | (have r₁ := eq802
       have r₂ := eq2997 y x
       grind)
    | (have r₁ := eq802
       have r₂ := eq2997 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq802
       have r₂ := eq2997 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq802 eq2997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802 eq2997
  have eq3733 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq3732
  have eq7310 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq809 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq809
    | (have j0 := eq809 (τ X1) (τ X0)
       grind)
    | exact resolve eq809 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq7377 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X1 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7310 X0 X1
       have i₂ := eq75 X1
       grind)
    | exact superpose eq75 eq7310
    | (have j0 := eq7310 X0 X1
       grind)
    | exact resolve eq7310 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7310
  have eq7412 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7377 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq7377
    | (have j0 := eq7377 X0 X1
       grind)
    | exact resolve eq7377 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7377
  have eq7442 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7412 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7412
    | (have j0 := eq7412 X0 X1
       grind)
    | exact resolve eq7412 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7412
  have eq7467 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7442 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7442
    | (have j0 := eq7442 X0 X1
       grind)
    | exact resolve eq7442 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7442
  have eq7488 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7467 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7467
    | (have j0 := eq7467 X0 X1
       grind)
    | exact resolve eq7467 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7467
  have eq7508 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (M.op X1 X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7488 X0 X1
       have i₂ := eq75 X1
       grind)
    | exact superpose eq75 eq7488
    | (have j0 := eq7488 X0 X1
       grind)
    | exact resolve eq7488 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq7488
  have eq7523 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7508 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq7508
    | (have j0 := eq7508 X0 X1
       grind)
    | exact resolve eq7508 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7508
  have eq7537 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7523 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7523
    | (have j0 := eq7523 X0 X1
       grind)
    | exact resolve eq7523 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7523
  have eq7546 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7537 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7537
    | (have j0 := eq7537 X0 X1
       grind)
    | exact resolve eq7537 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7537
  have eq15898 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3733
       grind)
    | exact superpose eq3733 eq16
    | exact resolve eq16 eq3733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3733
  have eq15899 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq15898
       have r₂ := eq77 x
       grind)
    | exact resolve eq15898 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15898
  have eq15903 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq15899
       grind)
    | exact superpose eq15899 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15899
       grind)
    | exact resolve eq12 eq15899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15899
  have eq15905 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq15903
  have eq15909 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq93 x (σ y)
       have i₂ := eq15905
       grind)
    | exact superpose eq15905 eq93
    | (have j0 := eq93 x (σ y)
       grind)
    | (have r₁ := eq93 x (σ y)
       have r₂ := eq15905
       grind)
    | exact resolve eq93 eq15905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15905
  have eq15919 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq15909
  have eq15923 : (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15919
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq15919
    | exact resolve eq15919 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15919
  have eq15935 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq809 x y
       have i₂ := eq15923
       grind)
    | exact superpose eq15923 eq809
    | (have j0 := eq809 x y
       grind)
    | (have r₁ := eq809 x y
       have r₂ := eq15923
       grind)
    | exact resolve eq809 eq15923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15923
  have eq15956 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq15935
  have eq15957 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq15956
  have eq15962 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq809 x y
       grind)
    | (have r₁ := eq15957
       have r₂ := eq809 x y
       grind)
    | exact resolve eq15957 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809 eq15957
  have eq15967 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15962
       grind)
    | exact superpose eq15962 eq16
    | exact resolve eq16 eq15962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15968 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq93 x (σ y)
       have i₂ := eq15962
       grind)
    | exact superpose eq15962 eq93
    | (have j0 := eq93 x (σ y)
       grind)
    | (have r₁ := eq93 x (σ y)
       have r₂ := eq15962
       grind)
    | exact resolve eq93 eq15962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq15962
  have eq15978 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq15968
  have eq15982 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq15978
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq15978
    | exact resolve eq15978 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15978
  have eq15991 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15982
       grind)
    | exact superpose eq15982 eq10
    | exact resolve eq10 eq15982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15982
  have eq16153 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq15991
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15991
    | exact resolve eq15991 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15991
  have eq16521 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16153
       grind)
    | exact superpose eq16153 eq16
    | exact resolve eq16 eq16153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16153
  have eq16522 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq16521
       have r₂ := eq77 x
       grind)
    | exact resolve eq16521 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16521
  have eq16535 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq16522
       grind)
    | exact superpose eq16522 eq10
    | exact resolve eq10 eq16522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16522
  have eq16700 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq16535
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq16535
    | exact resolve eq16535 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16535
  have eq16724 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq7546 y x
       have i₂ := eq16700
       grind)
    | exact superpose eq16700 eq7546
    | (have j0 := eq7546 y x
       grind)
    | (have r₁ := eq7546 y x
       have r₂ := eq16700
       grind)
    | exact resolve eq7546 eq16700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7546 eq16700
  have eq16728 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq16724
  have eq16732 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15967
       have i₂ := eq16728
       grind)
    | exact superpose eq16728 eq15967
    | exact resolve eq15967 eq16728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15967 eq16728
  have eq16741 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq16732
  have eq16742 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16741
       grind)
    | exact superpose eq16741 eq16
    | exact resolve eq16 eq16741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16741
  have eq16745 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq16742
       have r₂ := eq77 x
       grind)
    | exact resolve eq16742 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16742
  have eq16746 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16745
       grind)
    | exact superpose eq16745 eq16
    | exact resolve eq16 eq16745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16747 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16745
       grind)
    | exact superpose eq16745 eq10
    | exact resolve eq10 eq16745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16745
  have eq16911 : x = y := by
    first
    | (have i₁ := eq16747
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16747
    | exact resolve eq16747 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16747
  have eq16912 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16746
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq16746
    | exact resolve eq16746 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq16746
  have eq16913 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16912
       have i₂ := eq16911
       grind)
    | exact superpose eq16911 eq16912
    | exact resolve eq16912 eq16911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16911 eq16912
  have eq16914 : False := by grind
  exact eq16914

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pyx_pyy_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  clear eq22
  have eq493 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq494 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq493 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq493 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq493 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq505 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq494 (σ X0)
       grind)
    | exact superpose eq494 eq15
    | exact resolve eq15 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq494 (τ X0)
       grind)
    | exact superpose eq494 eq31
    | exact resolve eq31 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq518 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq511 X0
       have i₂ := eq494 X0
       grind)
    | exact superpose eq494 eq511
    | exact resolve eq511 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq524 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq505 X0
       have i₂ := eq494 X0
       grind)
    | exact superpose eq494 eq505
    | exact resolve eq505 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq505
  have eq819 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq849 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq819 X0 X1
       have i₂ := eq524 X0
       grind)
    | exact superpose eq524 eq819
    | (have j0 := eq819 X0 X1
       grind)
    | exact resolve eq819 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq5096 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq849 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq849
    | exact resolve eq849 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq5177 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5096 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq5096
    | (have j0 := eq5096 X0 X1
       grind)
    | exact resolve eq5096 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5096
  have eq5181 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5177 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq5177 X1 (M.op (τ X1) (τ X1))
       have r₂ := eq12 (σ (M.op (τ X1) (τ X1))) X1
       grind)
    | (have r₁ := eq5177 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq5177 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5177
  have eq5182 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (τ (M.op X0 X0))) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5181 X0 X1
       have i₂ := eq518 X0
       grind)
    | exact superpose eq518 eq5181
    | (have j0 := eq5181 X0 X1
       grind)
    | exact resolve eq5181 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq5181
  have eq5183 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5182 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq5182
    | (have j0 := eq5182 X0 X1
       grind)
    | exact resolve eq5182 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5182
  have eq5184 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5183 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5183
    | exact resolve eq5183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5183
  have eq5388 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq5184 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq5184 X0 X1
       grind)
    | exact superpose eq5184 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq5184 X1 X0
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq5184 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq5184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5389 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq5184 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq5184 X0 X1
       grind)
    | exact superpose eq5184 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq5184 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq5184 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq5184 X0 X0
       grind)
    | exact resolve eq13 eq5184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5409 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5184 (σ y) (σ x)
       grind)
    | exact superpose eq5184 eq16
    | (have j1 := eq5184 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq5184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5443 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5389 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5389
  have eq5448 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5409
       have i₂ := eq524 x
       grind)
    | exact superpose eq524 eq5409
    | exact resolve eq5409 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5409
  have eq5449 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5388 X0 X1
       have j1 := eq5443 X0 X1
       grind)
    | (have r₁ := eq5388 X1 (k X1 X1)
       have r₂ := eq5443 X1 X1
       grind)
    | (have r₁ := eq5388 X0 (k X1 X0)
       have r₂ := eq5443 X0 X1
       grind)
    | (have r₁ := eq5388 X0 X1
       have r₂ := eq5443 X0 X1
       grind)
    | exact resolve eq5388 eq5443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5388 eq5443
  have eq5450 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq5448
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5448
    | exact resolve eq5448 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5448
  have eq5466 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5449 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5449
    | exact resolve eq5449 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5530 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq5449 X0 (τ X1)
       grind)
    | exact superpose eq5449 eq17
    | (have j1 := eq5449 X0 (τ X1)
       grind)
    | exact resolve eq17 eq5449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq5449
  have eq5650 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5466 X0 X1
       have i₂ := eq524 X1
       grind)
    | exact superpose eq524 eq5466
    | (have j0 := eq5466 X0 X1
       grind)
    | exact resolve eq5466 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524 eq5466
  have eq6784 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5530 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5530
    | exact resolve eq5530 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5530
  have eq6866 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6784 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6784
    | (have j0 := eq6784 X0 X1
       grind)
    | exact resolve eq6784 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6784
  have eq7803 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq5450
       have i₂ := eq5184 y x
       grind)
    | exact superpose eq5184 eq5450
    | (have j1 := eq5184 y x
       grind)
    | exact resolve eq5450 eq5184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7804 : (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq7803
  have eq8230 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5650 y x
       grind)
    | exact superpose eq5650 eq16
    | (have j1 := eq5650 y x
       grind)
    | exact resolve eq16 eq5650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5650
  have eq8337 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq8230
       have i₂ := eq7804
       grind)
    | exact superpose eq7804 eq8230
    | exact resolve eq8230 eq7804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7804 eq8230
  have eq8346 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq8337
  have eq8347 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq8346
       have r₂ := eq5450
       grind)
    | exact resolve eq8346 eq5450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5450 eq8346
  have eq8349 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8347
       grind)
    | exact superpose eq8347 eq16
    | exact resolve eq16 eq8347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8347
  have eq8386 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq8349
       have i₂ := eq6866 y x
       grind)
    | exact superpose eq6866 eq8349
    | (have j1 := eq6866 y x
       grind)
    | (have r₁ := eq8349
       have r₂ := eq6866 y x
       grind)
    | exact resolve eq8349 eq6866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6866
  have eq8387 : (k y x) = (M.op x x) := by grind
  clear eq8386
  have eq8396 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8349
       have i₂ := eq8387
       grind)
    | exact superpose eq8387 eq8349
    | exact resolve eq8349 eq8387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8349
  have eq8452 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq8396
       have i₂ := eq5184 y x
       grind)
    | exact superpose eq5184 eq8396
    | (have j1 := eq5184 y x
       grind)
    | exact resolve eq8396 eq5184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5184
  have eq8453 : (M.op x y) = (k y x) := by grind
  clear eq8452
  have eq8454 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq8453
       have i₂ := eq8387
       grind)
    | exact superpose eq8387 eq8453
    | exact resolve eq8453 eq8387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8387 eq8453
  have eq8455 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8396
       have i₂ := eq8454
       grind)
    | exact superpose eq8454 eq8396
    | exact resolve eq8396 eq8454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8396 eq8454
  have eq8472 : False := by grind
  exact eq8472

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq122 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq83 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq83 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq125 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq122 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq126 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq125 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq128 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq126 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq126
    | (have j0 := eq126 X0 X1
       grind)
    | exact resolve eq126 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq132 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq128 X0 X1
       have j1 := eq124 X1 X0
       grind)
    | (have r₁ := eq128 X1 X0
       have r₂ := eq124 X0 X1
       grind)
    | (have r₁ := eq128 (k X1 X0) X1
       have r₂ := eq124 X0 X1
       grind)
    | (have r₁ := eq128 X1 X1
       have r₂ := eq124 X1 X1
       grind)
    | exact resolve eq128 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq128
  have eq512 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq132 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq132
    | exact resolve eq132 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq132 y x
       grind)
    | exact superpose eq132 eq16
    | (have j1 := eq132 y x
       grind)
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq540 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq512 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq512
    | (have j0 := eq512 X0 X1
       grind)
    | exact resolve eq512 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq512
  have eq541 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq540 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq540
    | exact resolve eq540 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq600 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq541 (τ X1) X0
       grind)
    | exact superpose eq541 eq18
    | (have j1 := eq541 (τ X1) X0
       grind)
    | exact resolve eq18 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq541
  have eq797 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq600 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq600
    | exact resolve eq600 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq856 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq797 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq797
    | (have j0 := eq797 X0 X1
       grind)
    | exact resolve eq797 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq969 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq526
       have i₂ := eq856 y x
       grind)
    | exact superpose eq856 eq526
    | (have j1 := eq856 (σ y) (σ x)
       grind)
    | (have r₁ := eq526
       have r₂ := eq856 y x
       grind)
    | exact resolve eq526 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq970 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq969
  have eq975 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq970
  have eq1022 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq526
       have i₂ := eq975
       grind)
    | exact superpose eq975 eq526
    | exact resolve eq526 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq975
  have eq1023 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1022
  have eq1024 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1023
  have eq1035 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1024
  have eq1043 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1035
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1035
    | exact resolve eq1035 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1080 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1043
       grind)
    | exact superpose eq1043 eq16
    | exact resolve eq16 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1089 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1080
       have i₂ := eq856 y x
       grind)
    | exact superpose eq856 eq1080
    | (have j1 := eq856 y x
       grind)
    | (have r₁ := eq1080
       have r₂ := eq856 y x
       grind)
    | exact resolve eq1080 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq1090 : y = (M.op x x) := by grind
  clear eq1089
  have eq1127 : (M.op x y) = (k y x) := by grind
  clear eq1090
  have eq1134 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1080
       have i₂ := eq1127
       grind)
    | exact superpose eq1127 eq1080
    | exact resolve eq1080 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080 eq1127
  have eq1137 : False := by grind
  exact eq1137

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq38 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq74 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq75 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq125 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq4246 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq75 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq75 (σ X1) X1
       grind)
    | exact resolve eq13 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4290 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq4291 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4290 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4290
  have eq4295 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4246 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4246
  have eq4296 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4295 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4295
  have eq4298 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4291 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4291
    | (have j0 := eq4291 X0
       grind)
    | exact resolve eq4291 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4291
  have eq4346 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq4298 X0
       grind)
    | exact superpose eq4298 eq38
    | (have j1 := eq4298 X0
       grind)
    | exact resolve eq38 eq4298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq4298
  have eq4357 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4346 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4346
    | (have j0 := eq4346 X0
       grind)
    | exact resolve eq4346 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4346
  have eq4358 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4357 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4357
  have eq4360 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4358 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4358
    | exact resolve eq4358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4385 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4358 X0
       grind)
    | exact superpose eq4358 eq11
    | exact resolve eq11 eq4358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4358
  have eq4447 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4360 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq4360
    | exact resolve eq4360 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4360
  have eq4665 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4447 X0
       grind)
    | exact superpose eq4447 eq11
    | exact resolve eq11 eq4447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4777 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4665 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4665
    | exact resolve eq4665 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4665
  have eq4839 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq4777 (τ X0)
       grind)
    | exact superpose eq4777 eq34
    | exact resolve eq34 eq4777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4894 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4839 X0
       have i₂ := eq4447 X0
       grind)
    | exact superpose eq4447 eq4839
    | exact resolve eq4839 eq4447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4447 eq4839
  have eq5436 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5454 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5436 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5436
    | exact resolve eq5436 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5436
  have eq5485 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5454 X0
       have i₂ := eq4777 X0
       grind)
    | exact superpose eq4777 eq5454
    | exact resolve eq5454 eq4777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5454
  have eq5500 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq5485
  have eq20975 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1) X0
       have i₂ := eq4296 (σ X0) X1
       grind)
    | exact superpose eq4296 eq24
    | (have j1 := eq4296 (σ X0) X1
       grind)
    | exact resolve eq24 eq4296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4296
  have eq21064 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq20975 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq20975
    | (have j0 := eq20975 X0 X1
       grind)
    | exact resolve eq20975 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20975
  have eq21137 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq21064 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21064
    | (have j0 := eq21064 X0 X1
       grind)
    | exact resolve eq21064 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21064
  have eq21201 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq21137 X0 X1
       have i₂ := eq4385 X0
       grind)
    | exact superpose eq4385 eq21137
    | (have j0 := eq21137 X0 X1
       grind)
    | exact resolve eq21137 eq4385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21137
  have eq21244 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq21201 X0 X1
       have i₂ := eq4777 X0
       grind)
    | exact superpose eq4777 eq21201
    | (have j0 := eq21201 X0 X1
       grind)
    | exact resolve eq21201 eq4777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21201
  have eq21278 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21244 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21244
    | (have j0 := eq21244 X0 X1
       grind)
    | exact resolve eq21244 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21244
  have eq25130 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (σ (M.op X1 X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21278 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21278
    | (have j0 := eq21278 X1 (τ X0)
       grind)
    | exact resolve eq21278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25182 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq21278 X1 X0
       grind)
    | exact superpose eq21278 eq11
    | (have j1 := eq21278 X1 X0
       grind)
    | exact resolve eq11 eq21278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21278
  have eq25604 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (M.op (τ X1) (τ X1))) = X0 ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25130 X1 (τ X0)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq25130
    | (have j0 := eq25130 X0 (τ X1)
       grind)
    | exact resolve eq25130 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq25130
  have eq25797 : ∀ X0 X1 : G, (σ (τ (M.op X1 X1))) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25604 X0 X1
       have i₂ := eq4894 X1
       grind)
    | exact superpose eq4894 eq25604
    | (have j0 := eq25604 X0 X1
       grind)
    | exact resolve eq25604 eq4894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4894 eq25604
  have eq25881 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25797 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq25797
    | (have j0 := eq25797 X0 X1
       grind)
    | exact resolve eq25797 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25797
  have eq25956 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25881 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq25881
    | (have j0 := eq25881 X0 X1
       grind)
    | exact resolve eq25881 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25881
  have eq26839 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq25956 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25956
  have eq28400 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25182 y x
       grind)
    | exact superpose eq25182 eq16
    | (have j1 := eq25182 y x
       grind)
    | exact resolve eq16 eq25182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25182
  have eq28778 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq28400
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq28400
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq28400 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28400
  have eq28781 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq28778
  have eq28782 : x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq28781
  have eq29005 : (τ x) ≠ (τ x) ∨ y = (M.op x x) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26839 y x
       have i₂ := eq28782
       grind)
    | exact superpose eq28782 eq26839
    | (have j0 := eq26839 y x
       grind)
    | exact resolve eq26839 eq28782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26839
  have eq29006 : (τ x) ≠ (τ x) ∨ y = (M.op x x) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq29005
  have eq29007 : y = (M.op x x) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq29006
  have eq29260 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5500 x
       have i₂ := eq29007
       grind)
    | exact superpose eq29007 eq5500
    | exact resolve eq5500 eq29007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29007
  have eq29281 : (σ y) = (σ (M.op x x)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have r₁ := eq29260
       have r₂ := eq16
       grind)
    | exact resolve eq29260 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29260
  have eq29299 : (M.op x x) = (τ (σ y)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq29281
       grind)
    | exact superpose eq29281 eq10
    | exact resolve eq10 eq29281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29281
  have eq29426 : y = (M.op x x) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq29299
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq29299
    | exact resolve eq29299 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29299
  have eq30069 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq5500 x
       have i₂ := eq29426
       grind)
    | exact superpose eq29426 eq5500
    | exact resolve eq5500 eq29426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29426
  have eq30090 : (τ x) = (τ (k y x)) := by
    first
    | (have r₁ := eq30069
       have r₂ := eq16
       grind)
    | exact resolve eq30069 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30069
  have eq30105 : (k y x) = (σ (τ x)) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq30090
       grind)
    | exact superpose eq30090 eq11
    | exact resolve eq11 eq30090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30090
  have eq30276 : x = (k y x) := by
    first
    | (have i₁ := eq30105
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq30105
    | exact resolve eq30105 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30105
  have eq30557 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq125 x y
       have i₂ := eq30276
       grind)
    | exact superpose eq30276 eq125
    | (have j0 := eq125 x y
       grind)
    | exact resolve eq125 eq30276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq30276
  have eq30565 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq30557
  have eq30569 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30565
       have i₂ := eq4385 x
       grind)
    | exact superpose eq4385 eq30565
    | exact resolve eq30565 eq4385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4385 eq30565
  have eq30574 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq30569
       have i₂ := eq4777 x
       grind)
    | exact superpose eq4777 eq30569
    | exact resolve eq30569 eq4777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4777 eq30569
  have eq33573 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30574
       grind)
    | exact superpose eq30574 eq16
    | exact resolve eq16 eq30574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30574
  have eq34054 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33573
       have i₂ := eq28782
       grind)
    | exact superpose eq28782 eq33573
    | exact resolve eq33573 eq28782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28782 eq33573
  have eq34055 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq34054
  have eq34056 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq34055
  have eq34070 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5500 x
       have i₂ := eq34056
       grind)
    | exact superpose eq34056 eq5500
    | exact resolve eq5500 eq34056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34056
  have eq34091 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq34070
       have r₂ := eq16
       grind)
    | exact resolve eq34070 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34070
  have eq34532 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq34091
       grind)
    | exact superpose eq34091 eq10
    | exact resolve eq10 eq34091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34091
  have eq34662 : y = (M.op x x) := by
    first
    | (have i₁ := eq34532
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq34532
    | exact resolve eq34532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34532
  have eq34758 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5500 x
       have i₂ := eq34662
       grind)
    | exact superpose eq34662 eq5500
    | exact resolve eq5500 eq34662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5500 eq34662
  have eq34779 : False := by grind
  exact eq34779

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
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
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | (have j0 := eq42 X0 X1
       have j1 := eq36 X1 X0
       grind)
    | (have r₁ := eq42 X1 X0
       have r₂ := eq36 X0 X1
       grind)
    | exact resolve eq42 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq42
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
  have eq94 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq98 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq94 X0 X1
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq94 X1 X1
       have r₂ := eq47 X1 X1
       grind)
    | exact resolve eq94 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq94
  have eq228 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq98 (σ X0) (σ X1)
       grind)
    | exact superpose eq98 eq15
    | exact resolve eq15 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq228 X0 X1
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq228
    | exact resolve eq228 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq228
  have eq238 : False := by grind
  exact eq238

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation3112 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3112 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  clear eq19
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq465 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq470 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq473 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
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
  have eq482 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq465 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq465
    | (have j0 := eq465 X0 X1
       grind)
    | exact resolve eq465 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq887 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq482 x y
       grind)
    | exact superpose eq482 eq16
    | (have j1 := eq482 x y
       grind)
    | exact resolve eq16 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq3075 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq473 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq473
    | exact resolve eq473 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq3119 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3075 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3075
    | (have j0 := eq3075 X0 X1
       grind)
    | exact resolve eq3075 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075
  have eq3370 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq470 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq470 X0 X1
       grind)
    | exact superpose eq470 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq470 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq470 X0 (σ X0)
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq470 X0 X1
       grind)
    | exact resolve eq13 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq3375 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3370 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3370
  have eq3376 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3375 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3375
  have eq3642 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3376 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3376
    | exact resolve eq3376 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3376
  have eq3732 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3642 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3642
    | (have j0 := eq3642 X0 X1
       grind)
    | exact resolve eq3642 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3642
  have eq3760 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq3732 X0 X1
       grind)
    | exact superpose eq3732 eq11
    | (have j1 := eq3732 X0 X1
       grind)
    | exact resolve eq11 eq3732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3732
  have eq3878 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3760 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3760
    | (have j0 := eq3760 X0 X1
       grind)
    | exact resolve eq3760 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3760
  have eq3898 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3878 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3878
    | (have j0 := eq3878 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq3878 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3878
  have eq4056 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3898 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq3898
    | (have j0 := eq3898 X0 X1
       grind)
    | exact resolve eq3898 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3898
  have eq8788 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq887
       have i₂ := eq3119 x y
       grind)
    | exact superpose eq3119 eq887
    | (have j1 := eq3119 x y
       grind)
    | (have r₁ := eq887
       have r₂ := eq3119 x y
       grind)
    | (have r₁ := eq887
       have r₂ := eq3119 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq887
       have r₂ := eq3119 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq887 eq3119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8789 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq8788
  have eq11534 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4056 x y
       grind)
    | exact superpose eq4056 eq16
    | (have j1 := eq4056 x y
       grind)
    | exact resolve eq16 eq4056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4056
  have eq11621 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq11534
       have i₂ := eq3119 x y
       grind)
    | exact superpose eq3119 eq11534
    | (have j1 := eq3119 x y
       grind)
    | (have r₁ := eq11534
       have r₂ := eq3119 x y
       grind)
    | (have r₁ := eq11534
       have r₂ := eq3119 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq11534
       have r₂ := eq3119 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11534 eq3119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119
  have eq11622 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq11621
  have eq11751 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11622
       grind)
    | exact superpose eq11622 eq16
    | exact resolve eq16 eq11622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11622
  have eq11752 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq11751
       have r₂ := eq22 x
       grind)
    | exact resolve eq11751 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11751
  have eq23067 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq8789
       grind)
    | exact superpose eq8789 eq16
    | exact resolve eq16 eq8789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8789
  have eq23088 : x = y ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq23067
       have r₂ := eq11752
       grind)
    | exact resolve eq23067 eq11752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11752 eq23067
  have eq23093 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23088
       grind)
    | exact superpose eq23088 eq16
    | exact resolve eq16 eq23088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23088
  have eq23096 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq23093
       have r₂ := eq22 x
       grind)
    | exact resolve eq23093 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23093
  have eq23099 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (k X0 y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq23096
       grind)
    | exact superpose eq23096 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq23096
       grind)
    | exact resolve eq13 eq23096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23096
  have eq23239 : x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have j0 := eq23099 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23099
  have eq23248 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23239
       grind)
    | exact superpose eq23239 eq16
    | exact resolve eq16 eq23239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23239
  have eq23251 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq23248
       have r₂ := eq22 x
       grind)
    | exact resolve eq23248 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23248
  have eq23257 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq887
       have i₂ := eq23251
       grind)
    | exact superpose eq23251 eq887
    | exact resolve eq887 eq23251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq23258 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11534
       have i₂ := eq23251
       grind)
    | exact superpose eq23251 eq11534
    | exact resolve eq11534 eq23251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11534 eq23251
  have eq23276 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq23258
  have eq23277 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq23276
  have eq23278 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq23257
  have eq23279 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq23278
  have eq23283 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23277
       grind)
    | exact superpose eq23277 eq10
    | exact resolve eq10 eq23277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23277
  have eq23454 : x = y ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq23283
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23283
    | exact resolve eq23283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23283
  have eq23456 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23454
       grind)
    | exact superpose eq23454 eq16
    | exact resolve eq16 eq23454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23454
  have eq23459 : (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq23456
       have r₂ := eq22 x
       grind)
    | exact resolve eq23456 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23456
  have eq25330 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23279
       grind)
    | exact superpose eq23279 eq16
    | exact resolve eq16 eq23279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23279
  have eq25357 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq25330
       have r₂ := eq23459
       grind)
    | exact resolve eq25330 eq23459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23459 eq25330
  have eq25364 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25357
       grind)
    | exact superpose eq25357 eq16
    | exact resolve eq16 eq25357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25365 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25357
       grind)
    | exact superpose eq25357 eq10
    | exact resolve eq10 eq25357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25357
  have eq25553 : x = y := by
    first
    | (have i₁ := eq25365
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq25365
    | exact resolve eq25365 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25365
  have eq25554 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq25364
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq25364
    | exact resolve eq25364 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq25364
  have eq25558 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq25554
       have i₂ := eq25553
       grind)
    | exact superpose eq25553 eq25554
    | exact resolve eq25554 eq25553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25553 eq25554
  have eq25559 : False := by grind
  exact eq25559

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyy_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 X1) X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq68 X1 X2 X0
       grind)
    | exact superpose eq68 eq64
    | exact resolve eq64 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq186 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq184 (τ X0)
       grind)
    | exact superpose eq184 eq19
    | exact resolve eq19 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq558 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1454 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (k (M.op (σ X0) (σ X1)) (σ X2)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X1 X0) X2
       have i₂ := eq535 X1 X0
       grind)
    | exact superpose eq535 eq15
    | (have j1 := eq535 X1 X0
       grind)
    | exact resolve eq15 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1922 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq186 x
       have i₂ := eq558 (τ x) x
       grind)
    | exact superpose eq558 eq186
    | (have j1 := eq558 (τ X0) X0
       grind)
    | exact resolve eq186 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq558
  have eq1937 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1922 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922
  have eq1939 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1937 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1937
    | (have j0 := eq1937 X0
       grind)
    | exact resolve eq1937 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937
  have eq2027 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq1939 (τ X0)
       grind)
    | exact superpose eq1939 eq19
    | (have j1 := eq1939 (τ X0)
       grind)
    | exact resolve eq19 eq1939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939
  have eq2033 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2027 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2027
    | (have j0 := eq2027 X0
       grind)
    | exact resolve eq2027 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2027
  have eq2054 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2033 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2033
    | (have j0 := eq2033 X0
       grind)
    | exact resolve eq2033 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033
  have eq4385 : ∀ X0 X1 : G, (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) = (M.op X1 (M.op (M.op (τ (τ X0)) X1) (τ (τ X0)))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 (τ (τ X0)) (τ (τ X0))
       have i₂ := eq2054 X0
       grind)
    | exact superpose eq2054 eq86
    | (have j1 := eq2054 X0
       grind)
    | exact resolve eq86 eq2054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054
  have eq4432 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ X0)) = (M.op X1 (τ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4385 X0 X1
       have i₂ := eq64 (τ (τ X0)) X1
       grind)
    | exact superpose eq64 eq4385
    | (have j0 := eq4385 X0 X1
       grind)
    | exact resolve eq4385 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4385
  have eq6242 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq4432 (σ X0) X1
       grind)
    | exact superpose eq4432 eq23
    | (have j1 := eq4432 (σ X0) X1
       grind)
    | exact resolve eq23 eq4432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4432
  have eq6290 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6242 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq6242
    | (have j0 := eq6242 X0 X1
       grind)
    | exact resolve eq6242 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6242
  have eq6333 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6290 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6290
    | (have j0 := eq6290 X0 X1
       grind)
    | exact resolve eq6290 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6290
  have eq6369 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6333 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6333
    | (have j0 := eq6333 X0 X1
       grind)
    | exact resolve eq6333 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6333
  have eq6443 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq6369 (σ X0) X1
       grind)
    | exact superpose eq6369 eq23
    | (have j1 := eq6369 (σ X0) X1
       grind)
    | exact resolve eq23 eq6369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6369
  have eq6491 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6443 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq6443
    | (have j0 := eq6443 X0 X1
       grind)
    | exact resolve eq6443 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6443
  have eq6534 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6491 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6491
    | (have j0 := eq6491 X0 X1
       grind)
    | exact resolve eq6491 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6491
  have eq6570 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6534 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6534
    | (have j0 := eq6534 X0 X1
       grind)
    | exact resolve eq6534 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6534
  have eq6644 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq6570 (σ X0) X1
       grind)
    | exact superpose eq6570 eq23
    | (have j1 := eq6570 (σ X0) X1
       grind)
    | exact resolve eq23 eq6570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6570
  have eq6692 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6644 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq6644
    | (have j0 := eq6644 X0 X1
       grind)
    | exact resolve eq6644 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq6644
  have eq6733 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6692 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6692
    | (have j0 := eq6692 X0 X1
       grind)
    | exact resolve eq6692 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6692
  have eq9440 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq184 (σ X0)
       have i₂ := eq1454 X0 X0 X0
       grind)
    | exact superpose eq1454 eq184
    | (have j1 := eq1454 X0 X0 x
       grind)
    | exact resolve eq184 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq1454
  have eq9456 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq9440 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9440
  have eq9471 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq6733 eq9456
    | (have j0 := eq9456 X0
       have j1 := eq6733 X0 (σ X0)
       grind)
    | exact resolve eq9456 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6733 eq9456
  have eq9507 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq9471 (τ X0)
       grind)
    | exact superpose eq9471 eq19
    | (have j1 := eq9471 (τ X0)
       grind)
    | exact resolve eq19 eq9471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq9471
  have eq9583 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq9507 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9507
    | (have j0 := eq9507 X0
       grind)
    | exact resolve eq9507 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9507
  have eq9596 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9583 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9583
    | (have j0 := eq9583 X0
       grind)
    | exact resolve eq9583 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9583
  have eq9609 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq9596 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq9596 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq9596 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9596
  have eq9668 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq9609 (σ X0)
       grind)
    | exact superpose eq9609 eq15
    | exact resolve eq15 eq9609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9682 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq9609 (τ X0)
       grind)
    | exact superpose eq9609 eq32
    | exact resolve eq32 eq9609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq9714 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9682 X0
       have i₂ := eq9609 X0
       grind)
    | exact superpose eq9609 eq9682
    | exact resolve eq9682 eq9609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9682
  have eq9728 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9668 X0
       have i₂ := eq9609 X0
       grind)
    | exact superpose eq9609 eq9668
    | exact resolve eq9668 eq9609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9609 eq9668
  have eq9846 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 (τ X0) (τ X0) X1
       have i₂ := eq9714 X0
       grind)
    | exact superpose eq9714 eq68
    | exact resolve eq68 eq9714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9850 : ∀ X0 X1 : G, (M.op (M.op (τ X0) X1) (τ (M.op X0 X0))) = (M.op X1 (M.op (M.op (τ X0) X1) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 (τ X0) (τ X0)
       have i₂ := eq9714 X0
       grind)
    | exact superpose eq9714 eq86
    | exact resolve eq86 eq9714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9714
  have eq9901 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq535 X0 X1
       have i₂ := eq9728 X1
       grind)
    | exact superpose eq9728 eq535
    | (have j0 := eq535 X0 X1
       grind)
    | exact resolve eq535 eq9728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq9922 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq66 (σ X0) (σ X0)
       have i₂ := eq9728 X0
       grind)
    | exact superpose eq9728 eq66
    | exact resolve eq66 eq9728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq11089 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9901 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq9901
    | (have j0 := eq9901 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9901 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9901
  have eq22176 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11089 x y
       grind)
    | exact superpose eq11089 eq16
    | (have j1 := eq11089 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq11089 x y
       grind)
    | exact resolve eq16 eq11089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11089
  have eq22410 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq22176
  have eq99280 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq68 (σ x) (σ y) X0
       have i₂ := eq22410
       grind)
    | exact superpose eq22410 eq68
    | exact resolve eq68 eq22410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22410
  have eq99595 : ∀ X0 : G, (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) X0) = X0 ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq99280 X0
       have i₂ := eq64 (σ x) X0
       grind)
    | exact superpose eq64 eq99280
    | exact resolve eq99280 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99280
  have eq99747 : ∀ X0 : G, (M.op x x) = (τ (σ y)) ∨ (M.op (σ x) X0) = X0 ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq99595 X0
       grind)
    | exact superpose eq99595 eq10
    | (have j1 := eq99595 X0
       grind)
    | exact resolve eq10 eq99595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99595
  have eq99990 : ∀ X0 : G, y = (M.op x x) ∨ (M.op (σ x) X0) = X0 ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq99747 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq99747
    | (have j0 := eq99747 X0
       grind)
    | exact resolve eq99747 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99747
  have eq99991 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq99990 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99990
  have eq100021 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq99991 (σ y)
       grind)
    | exact superpose eq99991 eq16
    | exact resolve eq16 eq99991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100036 : ∀ X0 : G, (M.op (M.op (M.op (τ (σ x)) X0) (τ (σ x))) X0) = X0 ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9846 (σ x) X0
       have i₂ := eq99991 (σ x)
       grind)
    | exact superpose eq99991 eq9846
    | exact resolve eq9846 eq99991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9846
  have eq100040 : ∀ X0 : G, (M.op (M.op (τ (σ x)) X0) (τ (σ x))) = (M.op X0 (M.op (M.op (τ (σ x)) X0) (τ (σ x)))) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9850 (σ x) x
       have i₂ := eq99991 (σ x)
       grind)
    | exact superpose eq99991 eq9850
    | exact resolve eq9850 eq99991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9850 eq99991
  have eq100604 : ∀ X0 : G, (τ (σ x)) = (M.op X0 (τ (σ x))) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq100040 x
       have i₂ := eq64 (τ (σ x)) x
       grind)
    | exact superpose eq64 eq100040
    | exact resolve eq100040 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100040
  have eq100606 : ∀ X0 : G, (M.op (τ (σ x)) X0) = X0 ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq100036 X0
       have i₂ := eq64 (τ (σ x)) X0
       grind)
    | exact superpose eq64 eq100036
    | exact resolve eq100036 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100036
  have eq100683 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq100604 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq100604
    | exact resolve eq100604 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100604
  have eq100685 : ∀ X0 : G, y = (M.op x x) ∨ (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq100606 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq100606
    | exact resolve eq100606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100606
  have eq100971 : ∀ X0 : G, x = (M.op y x) ∨ x = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq64 x x
       have i₂ := eq100683 X0
       grind)
    | exact superpose eq100683 eq64
    | (have j1 := eq100683 y
       grind)
    | exact resolve eq64 eq100683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100683
  have eq101767 : x ≠ x ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq100971 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100971
  have eq101768 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq101767
  have eq101774 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64 y x
       have i₂ := eq101768
       grind)
    | exact superpose eq101768 eq64
    | exact resolve eq64 eq101768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101768
  have eq104946 : (σ y) ≠ (σ y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq100685 eq100021
    | exact resolve eq100021 eq100685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100021 eq100685
  have eq104947 : y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq104946
  have eq104992 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9922 x
       have i₂ := eq104947
       grind)
    | exact superpose eq104947 eq9922
    | exact resolve eq9922 eq104947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9922 eq104947
  have eq106311 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq104992
       grind)
    | exact superpose eq104992 eq16
    | exact resolve eq16 eq104992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104992
  have eq106556 : (σ y) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq101774 eq106311
    | exact resolve eq106311 eq101774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101774 eq106311
  have eq106557 : x = (M.op x y) := by grind
  clear eq106556
  have eq106581 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq106557
       grind)
    | exact superpose eq106557 eq16
    | exact resolve eq16 eq106557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106589 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 x y X0
       have i₂ := eq106557
       grind)
    | exact superpose eq106557 eq68
    | exact resolve eq68 eq106557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq106593 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op X0 (M.op (M.op x X0) x)) := by
    intro X0
    first
    | (have i₁ := eq86 X0 x y
       have i₂ := eq106557
       grind)
    | exact superpose eq106557 eq86
    | exact resolve eq86 eq106557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq106899 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq106593 x
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq106593
    | exact resolve eq106593 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106593
  have eq106903 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq106589 X0
       have i₂ := eq64 x X0
       grind)
    | exact superpose eq64 eq106589
    | exact resolve eq106589 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq106589
  have eq108693 : x = y := by
    first
    | (have i₁ := eq106557
       have i₂ := eq106903 y
       grind)
    | exact superpose eq106903 eq106557
    | exact resolve eq106557 eq106903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106557 eq106903
  have eq109401 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq106581
       have i₂ := eq108693
       grind)
    | exact superpose eq108693 eq106581
    | exact resolve eq106581 eq108693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106581 eq108693
  have eq109402 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq109401
       have i₂ := eq9728 x
       grind)
    | exact superpose eq9728 eq109401
    | exact resolve eq109401 eq9728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9728 eq109401
  have eq109403 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq109402
       have i₂ := eq106899 x
       grind)
    | exact superpose eq106899 eq109402
    | exact resolve eq109402 eq106899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106899 eq109402
  have eq109404 : False := by grind
  exact eq109404

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pyx_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq17
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
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (M.op X0 X1) X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq67 X1 X2 X0
       grind)
    | exact superpose eq67 eq63
    | exact resolve eq63 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X1
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
  have eq454 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq453 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq453
    | (have j0 := eq453 X0 (σ X1)
       grind)
    | exact resolve eq453 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq453 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq453
    | (have j0 := eq453 X0 (τ X1)
       grind)
    | exact resolve eq453 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq465 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq453 X1 (τ X0)
       grind)
    | exact superpose eq453 eq18
    | (have j1 := eq453 X0 (τ X0)
       grind)
    | exact resolve eq18 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq642 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq454 X1 X0
       have i₂ := eq453 X1 X0
       grind)
    | exact superpose eq453 eq454
    | (have j0 := eq454 X0 X0
       have j1 := eq453 X0 (σ X0)
       grind)
    | exact resolve eq454 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (k (σ (M.op (τ X0) X1)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq465 X0 (M.op (τ X0) X1)
       have i₂ := eq65 (τ X0) X1
       grind)
    | exact superpose eq65 eq465
    | (have j0 := eq465 X0 X1
       grind)
    | exact resolve eq465 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq725 : ∀ X0 X1 : G, (k (σ X1) X0) = (k (k (σ X1) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | exact superpose eq465 eq709
    | (have j0 := eq709 X0 X1
       have j1 := eq465 X0 X1
       grind)
    | exact resolve eq709 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465 eq709
  have eq855 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq455 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq869 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq855 (σ X0)
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq855
    | (have j0 := eq855 (σ X0)
       grind)
    | exact resolve eq855 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq870 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq869 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq869
    | (have j0 := eq869 X0
       grind)
    | exact resolve eq869 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq873 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq870 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq870
    | (have j0 := eq870 X0
       grind)
    | exact resolve eq870 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq1896 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X1))) = (k (τ (k (σ X0) (σ X1))) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k (σ X0) (σ X1)) X1
       have i₂ := eq725 (σ X1) X0
       grind)
    | exact superpose eq725 eq22
    | (have j1 := eq725 (σ X1) X1
       grind)
    | exact resolve eq22 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq1912 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (k (k (τ (σ X0)) X1) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1896 X0 X1
       have i₂ := eq22 (σ X0) X1
       grind)
    | exact superpose eq22 eq1896
    | (have j0 := eq1896 X0 X1
       grind)
    | exact resolve eq1896 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1896
  have eq1922 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X1) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1912 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1912
    | (have j0 := eq1912 X0 X1
       grind)
    | exact resolve eq1912 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1912
  have eq1925 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (k (k X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1922 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1922
    | (have j0 := eq1922 X0 X1
       grind)
    | exact resolve eq1922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922
  have eq1927 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq453 eq1925
    | (have j0 := eq1925 X0 X1
       have j1 := eq453 X0 X1
       grind)
    | exact resolve eq1925 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq1925
  have eq1942 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1927 X0 (M.op X0 X1)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq1927
    | (have j0 := eq1927 X0 (M.op X0 X1)
       grind)
    | exact resolve eq1927 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927
  have eq2090 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) X2) = X2 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 (M.op X0 X1) (M.op X0 X1) X2
       have i₂ := eq1942 X0 X1
       grind)
    | exact superpose eq1942 eq67
    | (have j1 := eq1942 X0 X1
       grind)
    | exact resolve eq67 eq1942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2094 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) = (M.op X2 (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1))) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq85 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq1942 X0 X1
       grind)
    | exact superpose eq1942 eq85
    | (have j1 := eq1942 X0 X1
       grind)
    | exact resolve eq85 eq1942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq1942
  have eq2139 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X0 X1)) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2094 X0 X1 X1
       have i₂ := eq63 (M.op X0 X1) X1
       grind)
    | exact superpose eq63 eq2094
    | (have j0 := eq2094 X0 X1 X2
       grind)
    | exact resolve eq2094 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094
  have eq2141 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op (M.op X0 X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2090 X0 X1 X2
       have i₂ := eq63 (M.op X0 X1) X2
       grind)
    | exact superpose eq63 eq2090
    | (have j0 := eq2090 X0 X1 X2
       grind)
    | exact resolve eq2090 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090
  have eq2422 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (k X2 (M.op X0 X1)) = X2 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X1)
       have i₂ := eq2139 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq2139 eq13
    | (have j0 := eq13 X2 (M.op X0 X1)
       have j1 := eq2139 X0 X1 X2
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq2139 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2437 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (k X2 (M.op X0 X1)) = X2 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89 X2 (M.op X0 X1)
       have i₂ := eq2139 X0 X1 X2
       grind)
    | exact superpose eq2139 eq89
    | (have j0 := eq89 X0 X1
       have j1 := eq2139 X0 X1 X2
       grind)
    | (have r₁ := eq89 (M.op X0 X1) (M.op X0 X1)
       have r₂ := eq2139 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq89 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq2139
  have eq2519 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (k X2 (M.op X0 X1)) = X2 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq2422 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422
  have eq2555 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (k X2 (M.op X0 X1)) = X2 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq2141 eq2519
    | (have j0 := eq2519 X0 X1 X2
       have j1 := eq2141 X0 X1 X2
       grind)
    | exact resolve eq2519 eq2141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141 eq2519
  have eq2569 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 X1)) = X2 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq2555 X0 X1 X2
       have j1 := eq2437 X0 X1 X2
       grind)
    | (have r₁ := eq2555 X0 X1 X2
       have r₂ := eq2437 X0 X1 X2
       grind)
    | (have r₁ := eq2555 X0 X1 (M.op X0 X1)
       have r₂ := eq2437 X0 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq2555 X0 X1 (M.op X0 X1)
       have r₂ := eq2437 X0 X1 (k (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact resolve eq2555 eq2437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2437 eq2555
  have eq2858 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2569 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2569
  have eq2859 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2858 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858
  have eq2910 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) X1)
       have i₂ := eq2859 (σ X0) X1
       grind)
    | exact superpose eq2859 eq28
    | exact resolve eq28 eq2859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq2925 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2910 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2910
    | exact resolve eq2910 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2910
  have eq2948 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq642 x y
       grind)
    | exact superpose eq642 eq16
    | (have j1 := eq642 x x
       grind)
    | (have r₁ := eq16
       have r₂ := eq642 x y
       grind)
    | exact resolve eq16 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq3003 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq2948
  have eq3451 : x = (k x (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2925 x (σ x)
       have i₂ := eq3003
       grind)
    | exact superpose eq3003 eq2925
    | exact resolve eq2925 eq3003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2925 eq3003
  have eq3521 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3451
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3451
    | exact resolve eq3451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3451
  have eq3525 : x = (M.op x x) := by
    first
    | (have j1 := eq873 x
       grind)
    | (have r₁ := eq3521
       have r₂ := eq873 x
       grind)
    | exact resolve eq3521 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq3521
  have eq3534 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq67 x x X0
       have i₂ := eq3525
       grind)
    | exact superpose eq3525 eq67
    | exact resolve eq67 eq3525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3566 : x = (k x x) := by
    first
    | (have i₁ := eq2859 x x
       have i₂ := eq3525
       grind)
    | exact superpose eq3525 eq2859
    | exact resolve eq2859 eq3525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859 eq3525
  have eq3587 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3534 X0
       have i₂ := eq63 x X0
       grind)
    | exact superpose eq63 eq3534
    | exact resolve eq3534 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3534
  have eq3597 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq454 x x
       have i₂ := eq3566
       grind)
    | exact superpose eq3566 eq454
    | (have j0 := eq454 x x
       grind)
    | exact resolve eq454 eq3566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq3566
  have eq3600 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3597
  have eq3802 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3587 y
       grind)
    | exact superpose eq3587 eq16
    | exact resolve eq16 eq3587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587
  have eq4184 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq67 (σ x) (σ x) X0
       have i₂ := eq3600
       grind)
    | exact superpose eq3600 eq67
    | exact resolve eq67 eq3600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq3600
  have eq4237 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4184 X0
       have i₂ := eq63 (σ x) X0
       grind)
    | exact superpose eq63 eq4184
    | exact resolve eq4184 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq4184
  have eq4241 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq3802
       have i₂ := eq4237 (σ y)
       grind)
    | exact superpose eq4237 eq3802
    | (have r₁ := eq3802
       have r₂ := eq4237 (σ y)
       grind)
    | exact resolve eq3802 eq4237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3802 eq4237
  have eq4296 : False := by grind
  exact eq4296
