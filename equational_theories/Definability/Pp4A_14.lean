import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq93 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X2 X0) ∨ (M.op X0 X2) = X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 X0
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
  have eq120 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X2 X0) ∨ (M.op X0 X2) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq93 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq93 X1 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq93 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq93 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq2606 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq120 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq2607 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2606 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2606
  have eq2609 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2607 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq2607 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2607 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2607
  have eq2641 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2609 (σ X0) (σ X1)
       grind)
    | exact superpose eq2609 eq15
    | exact resolve eq15 eq2609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2652 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2641 X0 X1
       have i₂ := eq2609 X0 X1
       grind)
    | exact superpose eq2609 eq2641
    | exact resolve eq2641 eq2609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2609 eq2641
  have eq3376 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2652 x y
       grind)
    | exact superpose eq2652 eq16
    | (have r₁ := eq16
       have r₂ := eq2652 x y
       grind)
    | exact resolve eq16 eq2652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2652
  have eq3443 : False := by grind
  exact eq3443

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pyx_pyy_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    grind
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq14 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq14 eq63
    | exact resolve eq63 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq23 eq37
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq94
    | exact resolve eq94 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq380 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 X0) X1 x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) (M.op X4 X4)) = X3 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq14 X3 x X4
       have i₂ := eq52 X0 x X1
       grind)
    | (have i₁ := eq14 X0 (M.op x x) x
       have i₂ := eq52 x X1 x
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq433 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1
       have i₂ := eq52 X1 X0 X1
       grind)
    | (have i₁ := eq64 X0
       have i₂ := eq52 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq52 eq64
    | exact resolve eq64 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq497 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (σ (k X2 X2)) ∨ (σ X2) = (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (σ X2) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X1 X1
       have i₂ := eq52 X0 (σ X1) X2
       grind)
    | exact superpose eq52 eq74
    | exact resolve eq74 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq74
  have eq522 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (σ (k X2 X2)) ∨ (σ X2) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq497 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq5822 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (σ (M.op X0 X0)) ∨ (M.op (M.op X1 X1) (M.op X2 X2)) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq522 X1 X2 (M.op X0 X0)
       have i₂ := eq433 X0 X0
       grind)
    | exact superpose eq433 eq522
    | (have j0 := eq522 X1 X2 (M.op X0 X0)
       grind)
    | exact resolve eq522 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq522
  have eq5921 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq5822 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5822
  have eq6004 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq5921 X2 (M.op X0 X0) x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq5921
    | exact resolve eq5921 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6049 : ∀ X0 X3 X4 : G, (M.op (M.op (σ (M.op X0 X0)) X3) (M.op X4 X4)) = X3 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq384 x x X3 X4
       have i₂ := eq5921 X0 x x
       grind)
    | exact superpose eq5921 eq384
    | exact resolve eq384 eq5921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq5921
  have eq6278 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1)
       have i₂ := eq6004 X0 X1
       grind)
    | exact superpose eq6004 eq16
    | exact resolve eq16 eq6004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6282 : ∀ X0 X1 : G, (σ (k (M.op X1 X1) x)) = (k (M.op X0 X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (M.op X1 X1)
       have i₂ := eq6004 X0 X1
       grind)
    | exact superpose eq6004 eq40
    | exact resolve eq40 eq6004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq6004
  have eq6313 : ∀ X0 X1 : G, (σ (k (M.op X1 X1) x)) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6282 X0 X1
       have i₂ := eq410 X0 sF2
       grind)
    | exact superpose eq410 eq6282
    | exact resolve eq6282 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6282
  have eq6327 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X0)) = (σ (M.op x (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6313 X0 X1
       have i₂ := eq410 X1 x
       grind)
    | exact superpose eq410 eq6313
    | exact resolve eq6313 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq6313
  have eq34733 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq34734 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq34733
    | exact resolve eq34733 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34733
  have eq34745 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq34734
       have r₂ := eq28
       grind)
    | exact resolve eq34734 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34734
  have eq34747 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq34745
       have i₂ := eq380 X0 sF3
       grind)
    | (have i₁ := eq34745
       have i₂ := eq380 sF3 x
       grind)
    | exact superpose eq380 eq34745
    | exact resolve eq34745 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34745
  have eq35035 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq34747 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34747
  have eq35036 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq35035
  have eq35443 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq35036 eq6278
    | exact resolve eq6278 eq35036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6278 eq35036
  have eq35538 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 X0) = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq30 eq35443
    | exact resolve eq35443 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq35443
  have eq36179 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq35538 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35538
  have eq36180 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq36179
  have eq36210 : ∀ X0 : G, y = (M.op x x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq36180
       have i₂ := eq380 X0 y
       grind)
    | (have i₁ := eq36180
       have i₂ := eq380 y X0
       grind)
    | exact superpose eq380 eq36180
    | exact resolve eq36180 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36180
  have eq36502 : y ≠ y ∨ y = (M.op x x) := by
    first
    | (have j0 := eq36210 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36210
  have eq36503 : y = (M.op x x) := by grind
  clear eq36502
  have eq36534 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq36503
       have i₂ := eq380 X0 x
       grind)
    | (have i₁ := eq36503
       have i₂ := eq380 x X0
       grind)
    | exact superpose eq380 eq36503
    | exact resolve eq36503 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq36503
  have eq36831 : ∀ X1 : G, (σ (M.op x (M.op X1 X1))) = (M.op (σ x) y) := by
    intro X1
    first
    | (have i₁ := eq6327 x X1
       have i₂ := eq36534 x
       grind)
    | exact superpose eq36534 eq6327
    | exact resolve eq6327 eq36534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6327
  have eq36959 : ∀ X0 : G, y = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6049 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq36534 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq36534 eq6049
    | exact resolve eq6049 eq36534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6049
  have eq36998 : y = (σ y) := by
    first
    | (have i₁ := eq36959 x
       have i₂ := eq36534 x
       grind)
    | exact superpose eq36534 eq36959
    | exact resolve eq36959 eq36534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36959
  have eq37087 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq36831 x
       have i₂ := eq36534 x
       grind)
    | exact superpose eq36534 eq36831
    | exact resolve eq36831 eq36534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36534 eq36831
  have eq37212 : y = (σ y) := by
    first
    | (have i₁ := eq36998
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36998
    | exact resolve eq36998 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq36998
  have eq37260 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq37087
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq37087
    | exact resolve eq37087 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq37087
  have eq37334 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq21 eq37260
    | exact resolve eq37260 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq37260
  have eq37371 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq37212 eq27
    | exact resolve eq27 eq37212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq37212
  have eq39301 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37334 eq37371
    | exact resolve eq37371 eq37334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37334 eq37371
  have eq39302 : False := by grind
  exact eq39302

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq45
  have eq176 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq16 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq360 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq387 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq303
    | exact resolve eq303 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq548 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X0 x
       have i₂ := eq176 (M.op X0 X0) X1 x
       grind)
    | (have i₁ := eq16 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq176 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) (M.op X1 X1)) X2) = (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X1
       have i₂ := eq176 X0 X1 X2
       grind)
    | (have i₁ := eq179 (M.op X2 X2)
       have i₂ := eq176 X2 X1 X2
       grind)
    | exact superpose eq176 eq179
    | exact resolve eq179 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X1
       have i₂ := eq176 X0 X1 x
       grind)
    | (have i₁ := eq179 (M.op x x)
       have i₂ := eq176 x X1 x
       grind)
    | exact superpose eq176 eq179
    | exact resolve eq179 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq179
  have eq593 : ∀ X0 X1 X2 : G, (k (k (M.op X1 X1) (M.op X0 X0)) X2) = (M.op X2 (k (M.op X1 X1) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq585 X1 X0 X2
       have i₂ := eq587 X0 X1
       grind)
    | exact superpose eq587 eq585
    | exact resolve eq585 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585 eq587
  have eq1048 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1049 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1078 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1087 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1078 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1078 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq1078 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq1078 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq1078 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1125 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0 X1
       have i₂ := eq1087 X0
       grind)
    | exact superpose eq1087 eq548
    | exact resolve eq548 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq1190 : ∀ X0 X1 : G, (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1087 X0
       have i₂ := eq1125 X1 X0
       grind)
    | exact superpose eq1125 eq1087
    | exact resolve eq1087 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1202 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq1125 (σ X1) X0
       grind)
    | exact superpose eq1125 eq10
    | exact resolve eq10 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1203 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq360 X1 (σ X1)
       have i₂ := eq1125 (σ X1) X0
       grind)
    | exact superpose eq1125 eq360
    | exact resolve eq360 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq1204 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq387 X1 X1
       have i₂ := eq1125 (τ X1) X0
       grind)
    | exact superpose eq1125 eq387
    | exact resolve eq387 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1209 : ∀ X0 X1 : G, (k X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1203 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq1203
    | exact resolve eq1203 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1228 : ∀ X0 X1 : G, (k X1 X1) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1209 X0 X1
       have i₂ := eq1087 X0
       grind)
    | exact superpose eq1087 eq1209
    | exact resolve eq1209 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1558 : ∀ X0 X2 : G, (τ (k X0 X0)) = (σ (k X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq1202 x X2
       have i₂ := eq1204 x X0
       grind)
    | exact superpose eq1204 eq1202
    | exact resolve eq1202 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202 eq1204
  have eq2843 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1048
       grind)
    | exact superpose eq1048 eq40
    | exact resolve eq40 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2844 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq2843
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2843
    | exact resolve eq2843 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2843
  have eq2846 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq2844
    | exact resolve eq2844 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2844
  have eq2854 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2846 eq1049
    | exact resolve eq1049 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2861 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq2854
       have r₂ := eq27
       grind)
    | exact resolve eq2854 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2854
  have eq2866 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2861 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2861
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2861
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2861
       grind)
    | exact resolve eq12 eq2861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2861
  have eq2870 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq2866
       have r₂ := eq26
       grind)
    | exact resolve eq2866 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2866
  have eq2873 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq2870
       have i₂ := eq1087 sF2
       grind)
    | exact superpose eq1087 eq2870
    | exact resolve eq2870 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2870
  have eq2875 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2846 eq2873
    | exact resolve eq2873 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2846 eq2873
  have eq2876 : (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq2875
       have r₂ := eq27
       grind)
    | exact resolve eq2875 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2875
  have eq2883 : ∀ X0 : G, (σ y) = (k X0 X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2876 eq1190
    | exact resolve eq1190 eq2876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2887 : ∀ X0 : G, (τ (σ y)) = (k X0 X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2876 eq1228
    | exact resolve eq1228 eq2876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228 eq2876
  have eq2905 : ∀ X0 : G, y = (k X0 X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq32 eq2887
    | exact resolve eq2887 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2887
  have eq2915 : (M.op x y) = (M.op y x) ∨ y = (σ y) := by
    first
    | exact superpose eq2883 eq2905
    | exact resolve eq2905 eq2883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2883 eq2905
  have eq2925 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2915
       grind)
    | exact superpose eq2915 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2915
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq2915
       grind)
    | exact resolve eq12 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2915
  have eq2929 : y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (σ y) := by
    first
    | (have r₁ := eq2925
       have r₂ := eq18
       grind)
    | exact resolve eq2925 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2925
  have eq2932 : (M.op x y) = (k y x) ∨ y = (k x x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq2929
       have i₂ := eq1087 x
       grind)
    | exact superpose eq1087 eq2929
    | exact resolve eq2929 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929
  have eq3533 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq2932
       grind)
    | exact superpose eq2932 eq40
    | exact resolve eq40 eq2932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2932
  have eq3534 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq3533
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3533
    | exact resolve eq3533 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3533
  have eq3536 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq3534
    | exact resolve eq3534 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3534
  have eq3545 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (σ y) := by
    first
    | exact superpose eq3536 eq1049
    | exact resolve eq1049 eq3536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3552 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (σ y) := by
    first
    | (have r₁ := eq3545
       have r₂ := eq27
       grind)
    | exact resolve eq3545 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3545
  have eq3601 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ y = (σ y) := by
    first
    | exact superpose eq3552 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3552
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3552
       grind)
    | exact resolve eq12 eq3552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3552
  have eq3605 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ y = (σ y) := by
    first
    | (have r₁ := eq3601
       have r₂ := eq26
       grind)
    | exact resolve eq3601 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3601
  have eq3608 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq3605
       have i₂ := eq1087 sF2
       grind)
    | exact superpose eq1087 eq3605
    | exact resolve eq3605 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3605
  have eq3611 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (σ y) := by
    first
    | exact superpose eq3536 eq3608
    | exact resolve eq3608 eq3536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3536 eq3608
  have eq3612 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ y = (σ y) := by
    first
    | (have r₁ := eq3611
       have r₂ := eq27
       grind)
    | exact resolve eq3611 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3611
  have eq3617 : (τ (σ y)) = (k x x) ∨ y = (k x x) ∨ y = (σ y) := by
    first
    | exact superpose eq3612 eq98
    | exact resolve eq98 eq3612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq3612
  have eq3650 : y = (k x x) ∨ y = (k x x) ∨ y = (σ y) := by
    first
    | exact superpose eq32 eq3617
    | exact resolve eq3617 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3617
  have eq3651 : y = (k x x) ∨ y = (σ y) := by grind
  clear eq3650
  have eq3671 : ∀ X0 : G, y = (k X0 X0) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1190 x X0
       have i₂ := eq3651
       grind)
    | exact superpose eq3651 eq1190
    | exact resolve eq1190 eq3651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3682 : ∀ X0 : G, (σ y) = (τ (k X0 X0)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1558 X0 x
       have i₂ := eq3651
       grind)
    | exact superpose eq3651 eq1558
    | exact resolve eq1558 eq3651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558 eq3651
  have eq3691 : ∀ X0 : G, (σ y) = (τ (k X0 X0)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq3682 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3682
    | (have j0 := eq3682 X0
       grind)
    | exact resolve eq3682 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3682
  have eq3704 : (σ y) = (τ y) ∨ y = (σ y) := by
    first
    | exact superpose eq3671 eq3691
    | exact resolve eq3691 eq3671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3691
  have eq3817 : ∀ X0 : G, y = (τ (k X0 X0)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq387 X0 X0
       have i₂ := eq3671 (τ X0)
       grind)
    | exact superpose eq3671 eq387
    | exact resolve eq387 eq3671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq3843 : y = (τ y) ∨ y = (σ y) := by
    first
    | exact superpose eq3671 eq3817
    | exact resolve eq3817 eq3671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3671 eq3817
  have eq3883 : y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq3704 eq3843
    | exact resolve eq3843 eq3704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704 eq3843
  have eq3884 : y = (σ y) := by grind
  clear eq3883
  have eq3913 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3884
       grind)
    | exact superpose eq3884 eq18
    | exact resolve eq18 eq3884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3914 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3884
       grind)
    | exact superpose eq3884 eq24
    | exact resolve eq24 eq3884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq3917 : (M.op x y) = (k (σ y) x) ∨ (M.op x y) = (M.op (σ y) x) := by
    first
    | (have i₁ := eq1048
       have i₂ := eq3884
       grind)
    | exact superpose eq3884 eq1048
    | exact resolve eq1048 eq3884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048 eq3884
  have eq3992 : (M.op x y) ≠ (M.op (σ y) x) ∨ (σ y) = (M.op x x) ∨ (k (σ y) x) = (M.op (σ y) x) := by
    first
    | exact superpose eq3913 eq12
    | (have j0 := eq12 (σ y) x
       grind)
    | exact resolve eq12 eq3913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3994 : (M.op x y) ≠ (M.op (σ y) x) ∨ (σ y) = (k x x) ∨ (k (σ y) x) = (M.op (σ y) x) := by
    first
    | (have i₁ := eq3992
       have i₂ := eq1087 x
       grind)
    | exact superpose eq1087 eq3992
    | exact resolve eq3992 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992
  have eq4738 : (σ (M.op x y)) = (k (σ (σ y)) (σ x)) ∨ (M.op x y) = (M.op (σ y) x) := by
    first
    | exact superpose eq3917 eq40
    | exact resolve eq40 eq3917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3917
  have eq4739 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (σ y) x) := by
    first
    | exact superpose eq3914 eq4738
    | exact resolve eq4738 eq3914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4738
  have eq4742 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (σ y) x) := by
    first
    | exact superpose eq20 eq4739
    | exact resolve eq4739 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4739
  have eq4745 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op (σ y) x) := by
    first
    | exact superpose eq4742 eq1049
    | exact resolve eq1049 eq4742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4755 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op (σ y) x) := by
    first
    | (have r₁ := eq4745
       have r₂ := eq27
       grind)
    | exact resolve eq4745 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4745
  have eq4765 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (σ y) x) := by
    first
    | exact superpose eq4755 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq4755
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq4755
       grind)
    | exact resolve eq12 eq4755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4755
  have eq4769 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (σ y) x) := by
    first
    | (have r₁ := eq4765
       have r₂ := eq26
       grind)
    | exact resolve eq4765 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4765
  have eq4772 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (σ y) x) := by
    first
    | (have i₁ := eq4769
       have i₂ := eq1087 sF2
       grind)
    | exact superpose eq1087 eq4769
    | exact resolve eq4769 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4769
  have eq4774 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ y) x) := by
    first
    | exact superpose eq4742 eq4772
    | exact resolve eq4772 eq4742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4772
  have eq4775 : (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ y) x) := by
    first
    | (have r₁ := eq4774
       have r₂ := eq27
       grind)
    | exact resolve eq4774 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4774
  have eq4787 : ∀ X0 : G, (σ y) = (k X0 X0) ∨ (M.op x y) = (M.op (σ y) x) := by
    intro X0
    first
    | exact superpose eq4775 eq1190
    | exact resolve eq1190 eq4775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4775
  have eq255919 : ∀ X1 : G, (k (σ y) X1) = (M.op X1 (σ y)) ∨ (M.op x y) = (M.op (σ y) x) := by
    intro X1
    first
    | (have i₁ := eq593 X1 X1 x
       have i₂ := eq4787 (M.op X1 X1)
       grind)
    | exact superpose eq4787 eq593
    | exact resolve eq593 eq4787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4787
  have eq258684 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (σ y) x) := by
    first
    | exact superpose eq255919 eq26
    | (have j1 := eq255919 (σ x)
       grind)
    | exact resolve eq26 eq255919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255919
  have eq258685 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ y) x) := by
    first
    | exact superpose eq4742 eq258684
    | exact resolve eq258684 eq4742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4742 eq258684
  have eq258721 : (M.op x y) = (M.op (σ y) x) := by
    first
    | (have r₁ := eq258685
       have r₂ := eq27
       grind)
    | exact resolve eq258685 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258685
  have eq258750 : (M.op x y) ≠ (M.op x y) ∨ (σ y) = (k x x) ∨ (M.op x y) = (k (σ y) x) := by
    first
    | exact superpose eq258721 eq3994
    | (have r₁ := eq3994
       have r₂ := eq258721
       grind)
    | exact resolve eq3994 eq258721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3994 eq258721
  have eq258755 : (σ y) = (k x x) ∨ (M.op x y) = (k (σ y) x) := by grind
  clear eq258750
  have eq258800 : ∀ X0 : G, (σ y) = (k X0 X0) ∨ (M.op x y) = (k (σ y) x) := by
    intro X0
    first
    | (have i₁ := eq1190 x X0
       have i₂ := eq258755
       grind)
    | exact superpose eq258755 eq1190
    | exact resolve eq1190 eq258755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258755
  have eq261710 : ∀ X1 : G, (k (σ y) X1) = (M.op X1 (σ y)) ∨ (M.op x y) = (k (σ y) x) := by
    intro X1
    first
    | (have i₁ := eq593 X1 X1 x
       have i₂ := eq258800 (M.op X1 X1)
       grind)
    | exact superpose eq258800 eq593
    | exact resolve eq593 eq258800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258800
  have eq265532 : (M.op x y) = (k (σ y) x) ∨ (M.op x y) = (k (σ y) x) := by
    first
    | exact superpose eq261710 eq3913
    | exact resolve eq3913 eq261710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3913 eq261710
  have eq265534 : (M.op x y) = (k (σ y) x) := by grind
  clear eq265532
  have eq265545 : (σ (M.op x y)) = (k (σ (σ y)) (σ x)) := by
    first
    | exact superpose eq265534 eq40
    | exact resolve eq40 eq265534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq265534
  have eq265546 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3914 eq265545
    | exact resolve eq265545 eq3914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3914 eq265545
  have eq265552 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq265546
    | exact resolve eq265546 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq265546
  have eq265558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq265552 eq1049
    | exact resolve eq1049 eq265552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq265577 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq265558
       have r₂ := eq27
       grind)
    | exact resolve eq265558 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265558
  have eq265588 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq265577 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq265577
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq265577
       grind)
    | exact resolve eq12 eq265577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265577
  have eq265592 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq265588
       have r₂ := eq26
       grind)
    | exact resolve eq265588 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265588
  have eq265595 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq265592
       have i₂ := eq1087 sF2
       grind)
    | exact superpose eq1087 eq265592
    | exact resolve eq265592 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087 eq265592
  have eq265597 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq265552 eq265595
    | exact resolve eq265595 eq265552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265595
  have eq265598 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq265597
       have r₂ := eq27
       grind)
    | exact resolve eq265597 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265597
  have eq265616 : ∀ X0 : G, (σ y) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq265598 eq1190
    | exact resolve eq1190 eq265598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190 eq265598
  have eq268536 : ∀ X1 : G, (k (σ y) X1) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq593 X1 X1 x
       have i₂ := eq265616 (M.op X1 X1)
       grind)
    | exact superpose eq265616 eq593
    | exact resolve eq593 eq265616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq265616
  have eq273375 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq268536 eq26
    | (have j1 := eq268536 (σ x)
       grind)
    | exact resolve eq26 eq268536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq268536
  have eq273376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq265552 eq273375
    | exact resolve eq273375 eq265552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265552 eq273375
  have eq273412 : False := by grind
  exact eq273412

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    grind
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq14 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq14 eq63
    | exact resolve eq63 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
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
  have eq75 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq110
    | exact resolve eq110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq384 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 X0) X1 x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq534 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1
       have i₂ := eq52 X1 X0 X1
       grind)
    | (have i₁ := eq64 X0
       have i₂ := eq52 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq52 eq64
    | exact resolve eq64 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq682 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (σ (k X2 X2)) ∨ (σ X2) = (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (σ X2) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92 X1 X1
       have i₂ := eq52 X0 (σ X1) X2
       grind)
    | exact superpose eq52 eq92
    | exact resolve eq92 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq693 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq92 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq706 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (σ (k X2 X2)) ∨ (σ X2) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq682 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq6558 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (σ (M.op X0 X0)) ∨ (M.op (M.op X1 X1) (M.op X2 X2)) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq706 X1 X2 (M.op X0 X0)
       have i₂ := eq534 X0 X0
       grind)
    | exact superpose eq534 eq706
    | (have j0 := eq706 X1 X2 (M.op X0 X0)
       grind)
    | exact resolve eq706 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534 eq706
  have eq6656 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6558 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6558
  have eq6739 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq6656 X2 (M.op X0 X0) x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq6656
    | exact resolve eq6656 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7001 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1)
       have i₂ := eq6739 X0 X1
       grind)
    | exact superpose eq6739 eq16
    | exact resolve eq16 eq6739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14297 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14297
    | exact resolve eq14297 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14297
  have eq14309 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14298
       have r₂ := eq28
       grind)
    | exact resolve eq14298 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14298
  have eq14311 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14309
    | exact resolve eq14309 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14309
  have eq14317 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq14311
  have eq14382 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14317
    | exact resolve eq14317 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14317
  have eq14831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14382 eq112
    | exact resolve eq112 eq14382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14382
  have eq14840 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14831
  have eq14842 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14840
       have r₂ := eq28
       grind)
    | exact resolve eq14840 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14840
  have eq14850 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq14884 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6739 X0 x
       have i₂ := eq14842
       grind)
    | exact superpose eq14842 eq6739
    | exact resolve eq6739 eq14842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14842
  have eq14917 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14884 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14884
    | (have j0 := eq14884 X0
       grind)
    | exact resolve eq14884 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14884
  have eq14919 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14850
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14850
    | exact resolve eq14850 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14850
  have eq15408 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    grind
  clear eq14917
  have eq15839 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq14919
       grind)
    | exact superpose eq14919 eq71
    | exact resolve eq71 eq14919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14919
  have eq15855 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq15839
    | exact resolve eq15839 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15839
  have eq22614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15408 eq15855
    | exact resolve eq15855 eq15408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15408 eq15855
  have eq22627 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22614
  have eq22642 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq22627
    | exact resolve eq22627 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22627
  have eq22658 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq22642
       have r₂ := eq28
       grind)
    | exact resolve eq22642 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22642
  have eq22660 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22658 eq75
    | (have r₁ := eq75
       have r₂ := eq22658
       grind)
    | exact resolve eq75 eq22658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq22661 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22658 eq28
    | exact resolve eq28 eq22658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22658
  have eq22662 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq22660
  have eq26364 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22662 eq112
    | exact resolve eq112 eq22662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq22662
  have eq26384 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq26364
  have eq26398 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq26384
       have r₂ := eq22661
       grind)
    | exact resolve eq26384 eq22661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22661 eq26384
  have eq26452 : ∀ X0 : G, (τ (σ y)) = (M.op X0 X0) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26398 eq7001
    | exact resolve eq7001 eq26398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7001 eq26398
  have eq26518 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op X0 X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq26452
    | exact resolve eq26452 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq26452
  have eq26929 : y ≠ y ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq26518 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26518
  have eq26930 : y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq26929
  have eq26983 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  have eq27004 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq413 x x
       have i₂ := eq26930
       grind)
    | exact superpose eq26930 eq413
    | exact resolve eq413 eq26930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27018 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6739 X0 x
       have i₂ := eq26930
       grind)
    | exact superpose eq26930 eq6739
    | exact resolve eq6739 eq26930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6739
  have eq27093 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq27018 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27018
    | (have j0 := eq27018 X0
       grind)
    | exact resolve eq27018 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27018
  have eq27096 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26983
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26983
    | exact resolve eq26983 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26983
  have eq27848 : y = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26930
       have i₂ := eq27093 x
       grind)
    | exact superpose eq27093 eq26930
    | exact resolve eq26930 eq27093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26930 eq27093
  have eq27858 : y = (σ y) ∨ y = (M.op x y) := by grind
  clear eq27848
  have eq27906 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27858 eq27
    | exact resolve eq27 eq27858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq27096
       grind)
    | exact superpose eq27096 eq71
    | exact resolve eq71 eq27096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27096
  have eq28131 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq28108
    | exact resolve eq28108 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28108
  have eq28169 : (σ (M.op x y)) = (k y (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27858 eq28131
    | exact resolve eq28131 eq27858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27858 eq28131
  have eq28195 : (σ (M.op x y)) = (k y (σ x)) ∨ y = (M.op x y) := by grind
  clear eq28169
  have eq32225 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28195
       have i₂ := eq27004 sF2
       grind)
    | exact superpose eq27004 eq28195
    | exact resolve eq28195 eq27004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27004 eq28195
  have eq32230 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (M.op x y) := by grind
  clear eq32225
  have eq32608 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32230 eq27906
    | exact resolve eq27906 eq32230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27906 eq32230
  have eq32610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq32608
  have eq32612 : y = (M.op x y) := by
    first
    | (have r₁ := eq32610
       have r₂ := eq28
       grind)
    | exact resolve eq32610 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32610
  have eq32614 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq32612 eq21
    | exact resolve eq21 eq32612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq32619 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq32612 eq74
    | (have r₁ := eq74
       have r₂ := eq32612
       grind)
    | exact resolve eq74 eq32612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq32677 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq32619
  have eq32738 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq32614
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32614
    | exact resolve eq32614 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32614
  have eq32740 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq32738 eq27
    | exact resolve eq27 eq32738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq35439 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq32677
       grind)
    | exact superpose eq32677 eq71
    | exact resolve eq71 eq32677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35452 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq693 x y
       have i₂ := eq32677
       grind)
    | exact superpose eq32677 eq693
    | (have j0 := eq693 x y
       grind)
    | exact resolve eq693 eq32677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq32677
  have eq35455 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq35452
  have eq35462 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq35455
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq35455
    | exact resolve eq35455 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35455
  have eq35471 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32738 eq35439
    | exact resolve eq35439 eq32738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35439
  have eq35473 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32738 eq35462
    | exact resolve eq35462 eq32738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35462
  have eq35482 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq35471
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq35471
    | exact resolve eq35471 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35471
  have eq35483 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq35473
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq35473
    | exact resolve eq35473 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35473
  have eq35491 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32738 eq35482
    | exact resolve eq35482 eq32738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35482
  have eq35492 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32740 eq35483
    | exact resolve eq35483 eq32740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35483
  have eq35493 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq35492
       have r₂ := eq28
       grind)
    | exact resolve eq35492 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35492
  have eq35494 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq35493
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq35493
    | exact resolve eq35493 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq35493
  have eq35495 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq35494
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq35494
    | exact resolve eq35494 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35494
  have eq35496 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32738 eq35495
    | exact resolve eq35495 eq32738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35495
  have eq35576 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq35496
  have eq35692 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32740 eq35576
    | exact resolve eq35576 eq32740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35576
  have eq35973 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq35692 eq35491
    | exact resolve eq35491 eq35692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35491 eq35692
  have eq35977 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq35973
  have eq35979 : y = (M.op x x) := by
    first
    | (have r₁ := eq35977
       have r₂ := eq28
       grind)
    | exact resolve eq35977 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35977
  have eq35992 : ∀ X0 : G, y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq35979
       have i₂ := eq384 X0 x
       grind)
    | (have i₁ := eq35979
       have i₂ := eq384 x X0
       grind)
    | exact superpose eq384 eq35979
    | exact resolve eq35979 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq36008 : (M.op x y) = (k y x) := by grind
  have eq36029 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq413 x x
       have i₂ := eq35979
       grind)
    | exact superpose eq35979 eq413
    | exact resolve eq413 eq35979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq35979
  have eq36116 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq36008
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq36008
    | exact resolve eq36008 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq36008
  have eq36131 : y = (k y x) := by
    first
    | exact superpose eq32612 eq36116
    | exact resolve eq36116 eq32612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32612 eq36116
  have eq36320 : ∀ X1 : G, y = (σ (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq6656 X1 x x
       have i₂ := eq35992 (M.op x x)
       grind)
    | exact superpose eq35992 eq6656
    | exact resolve eq6656 eq35992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6656
  have eq36366 : y = (σ y) := by
    first
    | (have i₁ := eq36320 x
       have i₂ := eq35992 x
       grind)
    | exact superpose eq35992 eq36320
    | exact resolve eq36320 eq35992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35992 eq36320
  have eq36499 : y = (σ y) := by
    first
    | (have i₁ := eq36366
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36366
    | exact resolve eq36366 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36366
  have eq36577 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq32738 eq36499
    | exact resolve eq36499 eq32738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36499
  have eq36699 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq36577 eq32740
    | exact resolve eq32740 eq36577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32740
  have eq37355 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq36131
       grind)
    | exact superpose eq36131 eq71
    | exact resolve eq71 eq36131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq36131
  have eq37386 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq32738 eq37355
    | exact resolve eq37355 eq32738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37355
  have eq37396 : (σ y) = (k y (σ x)) := by
    first
    | exact superpose eq36577 eq37386
    | exact resolve eq37386 eq36577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37386
  have eq37406 : (σ y) = (k y (σ x)) := by
    first
    | (have i₁ := eq37396
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37396
    | exact resolve eq37396 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq37396
  have eq37415 : (σ (M.op x y)) = (k y (σ x)) := by
    first
    | exact superpose eq32738 eq37406
    | exact resolve eq37406 eq32738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32738 eq37406
  have eq37424 : y = (k y (σ x)) := by
    first
    | exact superpose eq36577 eq37415
    | exact resolve eq37415 eq36577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37415
  have eq37939 : y = (M.op (σ x) y) := by
    first
    | (have i₁ := eq37424
       have i₂ := eq36029 sF2
       grind)
    | exact superpose eq36029 eq37424
    | exact resolve eq37424 eq36029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36029 eq37424
  have eq37943 : y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36699 eq37939
    | exact resolve eq37939 eq36699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36699 eq37939
  have eq38377 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq37943 eq28
    | exact resolve eq28 eq37943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq37943
  have eq38380 : False := by grind
  exact eq38380

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    grind
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq14 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq14 eq63
    | exact resolve eq63 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ x = (k y x) := by
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
  have eq75 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq110
    | exact resolve eq110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq534 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1
       have i₂ := eq52 X1 X0 X1
       grind)
    | (have i₁ := eq64 X0
       have i₂ := eq52 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq52 eq64
    | exact resolve eq64 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq680 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (σ (k X2 X2)) ∨ (σ X2) = (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (σ X2) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92 X1 X1
       have i₂ := eq52 X0 (σ X1) X2
       grind)
    | exact superpose eq52 eq92
    | exact resolve eq92 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq691 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq92 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq704 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (σ (k X2 X2)) ∨ (σ X2) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq680 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq5666 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (σ (M.op X0 X0)) ∨ (M.op (M.op X1 X1) (M.op X2 X2)) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq704 X1 X2 (M.op X0 X0)
       have i₂ := eq534 X0 X0
       grind)
    | exact superpose eq534 eq704
    | (have j0 := eq704 X1 X2 (M.op X0 X0)
       grind)
    | exact resolve eq704 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534 eq704
  have eq5761 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq5666 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5666
  have eq5841 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq5761 X2 (M.op X0 X0) x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq5761
    | exact resolve eq5761 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5761
  have eq15278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15279 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15278
    | exact resolve eq15278 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15278
  have eq15287 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15279
       have r₂ := eq28
       grind)
    | exact resolve eq15279 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15279
  have eq15289 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15287
    | exact resolve eq15287 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15287
  have eq15295 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq15289
  have eq15379 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15295
    | exact resolve eq15295 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15295
  have eq15862 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15379 eq112
    | exact resolve eq112 eq15379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15379
  have eq15868 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15862
  have eq15870 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15868
       have r₂ := eq28
       grind)
    | exact resolve eq15868 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15868
  have eq15878 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq15912 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5841 X0 x
       have i₂ := eq15870
       grind)
    | exact superpose eq15870 eq5841
    | exact resolve eq5841 eq15870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5841 eq15870
  have eq15959 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15912 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15912
    | (have j0 := eq15912 X0
       grind)
    | exact resolve eq15912 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15912
  have eq15961 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15878
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15878
    | exact resolve eq15878 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15878
  have eq16480 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    grind
  clear eq15959
  have eq16944 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq15961
       grind)
    | exact superpose eq15961 eq71
    | exact resolve eq71 eq15961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15961
  have eq16960 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq16944
    | exact resolve eq16944 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16944
  have eq23747 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16480 eq16960
    | exact resolve eq16960 eq16480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16480 eq16960
  have eq23757 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23747
  have eq23769 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq23757
    | exact resolve eq23757 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23757
  have eq23782 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23769
       have r₂ := eq28
       grind)
    | exact resolve eq23769 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23769
  have eq23784 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23782 eq75
    | (have r₁ := eq75
       have r₂ := eq23782
       grind)
    | exact resolve eq75 eq23782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq23785 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23782 eq28
    | exact resolve eq28 eq23782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23786 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq23784
  have eq28208 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq23786
  have eq28335 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq28208
    | exact resolve eq28208 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28208
  have eq28927 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq112 eq28335
    | exact resolve eq28335 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq28943 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq28335
  have eq28950 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq28927
  have eq28952 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq28943
       have r₂ := eq23782
       grind)
    | exact resolve eq28943 eq23782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23782 eq28943
  have eq28953 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq28950
       have r₂ := eq23785
       grind)
    | exact resolve eq28950 eq23785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23785 eq28950
  have eq28955 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq28953
       have r₂ := eq28
       grind)
    | exact resolve eq28953 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28953
  have eq28964 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28952 eq81
    | exact resolve eq81 eq28952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq28952
  have eq28994 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq28964
    | exact resolve eq28964 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28964
  have eq29012 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq28955
  have eq29143 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29012
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29012
    | exact resolve eq29012 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29012
  have eq30454 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28994
       have i₂ := eq29143
       grind)
    | exact superpose eq29143 eq28994
    | exact resolve eq28994 eq29143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28994 eq29143
  have eq30459 : x = (M.op x y) := by grind
  clear eq30454
  have eq30473 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq30459 eq21
    | exact resolve eq21 eq30459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq30478 : x ≠ x ∨ y = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq30459 eq74
    | (have r₁ := eq74
       have r₂ := eq30459
       grind)
    | exact resolve eq74 eq30459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq30536 : y = (M.op x x) ∨ x = (k y x) := by grind
  clear eq30478
  have eq30597 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq30473
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30473
    | exact resolve eq30473 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30473
  have eq30598 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq30597 eq27
    | exact resolve eq27 eq30597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32586 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq30536
  have eq32699 : (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq32586
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32586
    | exact resolve eq32586 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq32586
  have eq32701 : x = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq30459 eq32699
    | exact resolve eq32699 eq30459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30459 eq32699
  have eq32702 : x = (k y x) := by grind
  clear eq32701
  have eq32708 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq32702
       grind)
    | exact superpose eq32702 eq71
    | exact resolve eq71 eq32702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq32720 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq691 x y
       have i₂ := eq32702
       grind)
    | exact superpose eq32702 eq691
    | (have j0 := eq691 x y
       grind)
    | exact resolve eq691 eq32702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq32702
  have eq32723 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq32720
  have eq32730 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq32723
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32723
    | exact resolve eq32723 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32723
  have eq32739 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq30597 eq32708
    | exact resolve eq32708 eq30597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32708
  have eq32741 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq32730
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32730
    | exact resolve eq32730 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32730
  have eq32750 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq32739
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32739
    | exact resolve eq32739 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32739
  have eq32751 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq32741
    | exact resolve eq32741 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32741
  have eq32759 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq30597 eq32750
    | exact resolve eq32750 eq30597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32750
  have eq32760 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq30597 eq32751
    | exact resolve eq32751 eq30597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32751
  have eq32761 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq32760
       have r₂ := eq28
       grind)
    | exact resolve eq32760 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32760
  have eq32762 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq32761
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32761
    | exact resolve eq32761 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq32761
  have eq32763 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq30597 eq32762
    | exact resolve eq32762 eq30597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30597 eq32762
  have eq32764 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq32763
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32763
    | exact resolve eq32763 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq32763
  have eq32817 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq32764
  have eq32929 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq30598 eq32817
    | exact resolve eq32817 eq30598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30598 eq32817
  have eq32930 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32759 eq32929
    | exact resolve eq32929 eq32759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32759 eq32929
  have eq32931 : False := by grind
  exact eq32931

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    grind
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq14 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq14 eq64
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq83 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq101
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq107
    | exact resolve eq107 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq380 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X0 X0) X1 x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq429 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X1
       have i₂ := eq53 X1 X0 X1
       grind)
    | (have i₁ := eq65 X0
       have i₂ := eq53 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq53 eq65
    | exact resolve eq65 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq475 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (σ (k X2 X2)) ∨ (σ X2) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 X0
       have i₂ := eq53 X0 (σ X0) X2
       grind)
    | exact superpose eq53 eq75
    | exact resolve eq75 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq75
  have eq6814 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (σ (M.op X0 X0)) ∨ (M.op (M.op X1 X1) (M.op X2 X2)) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq475 X1 X2 (M.op X0 X0)
       have i₂ := eq429 X0 X0
       grind)
    | exact superpose eq429 eq475
    | (have j0 := eq475 X1 X2 (M.op X0 X0)
       grind)
    | exact resolve eq475 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq475
  have eq6912 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6814 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6814
  have eq6992 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq6912 X2 (M.op X0 X0) x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq6912
    | exact resolve eq6912 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13965 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq13965
    | exact resolve eq13965 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13965
  have eq13977 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq13966
       have r₂ := eq29
       grind)
    | exact resolve eq13966 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13966
  have eq13983 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq13977
  have eq14047 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq13983
    | exact resolve eq13983 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13983
  have eq14429 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq14047 eq108
    | exact resolve eq108 eq14047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq14047
  have eq14438 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq14429
  have eq14441 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14438
       have r₂ := eq29
       grind)
    | exact resolve eq14438 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14438
  have eq14448 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  have eq14469 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq407 x x
       have i₂ := eq14441
       grind)
    | exact superpose eq14441 eq407
    | exact resolve eq407 eq14441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq14482 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6992 X0 x
       have i₂ := eq14441
       grind)
    | exact superpose eq14441 eq6992
    | exact resolve eq6992 eq14441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6992
  have eq14514 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14482 X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq14482
    | (have j0 := eq14482 X0
       grind)
    | exact resolve eq14482 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14482
  have eq14516 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14448
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14448
    | exact resolve eq14448 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14448
  have eq15101 : y = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14441
       have i₂ := eq14514 x
       grind)
    | exact superpose eq14514 eq14441
    | exact resolve eq14441 eq14514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14441 eq14514
  have eq15106 : (σ x) = (σ y) ∨ x = y ∨ y = (σ y) := by grind
  clear eq15101
  have eq15226 : y = (τ (σ x)) ∨ x = y ∨ y = (σ y) := by
    first
    | exact superpose eq15106 eq31
    | exact resolve eq31 eq15106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15106
  have eq15343 : x = y ∨ x = y ∨ y = (σ y) := by
    first
    | exact superpose eq30 eq15226
    | exact resolve eq15226 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15226
  have eq15344 : y = (σ y) ∨ x = y := by grind
  clear eq15343
  have eq15346 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ x = y := by
    first
    | exact superpose eq15344 eq28
    | exact resolve eq28 eq15344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15355 : (k y x) = (τ (k y (σ x))) ∨ x = y := by
    first
    | exact superpose eq15344 eq83
    | exact resolve eq83 eq15344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq15344
  have eq15806 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq14516
       grind)
    | exact superpose eq14516 eq72
    | exact resolve eq72 eq14516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14516
  have eq15822 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq15806
    | exact resolve eq15806 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15806
  have eq15962 : (σ (k y x)) = (k y (σ x)) ∨ x = y := by
    first
    | exact superpose eq15355 eq15
    | exact resolve eq15 eq15355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15355
  have eq15997 : (k (σ y) (σ x)) = (k y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq15962
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq15962
    | exact resolve eq15962 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq15962
  have eq16014 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq15997 eq15822
    | exact resolve eq15822 eq15997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15822 eq15997
  have eq16016 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16014
  have eq68732 : (σ (M.op x y)) = (M.op (σ x) y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16016
       have i₂ := eq14469 sF2
       grind)
    | exact superpose eq14469 eq16016
    | exact resolve eq16016 eq14469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14469 eq16016
  have eq68813 : (σ (M.op x y)) = (M.op (σ x) y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq68732
  have eq69312 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq68813 eq15346
    | exact resolve eq15346 eq68813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15346 eq68813
  have eq69313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq69312
  have eq69315 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq69313
       have r₂ := eq29
       grind)
    | exact resolve eq69313 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69313
  have eq69319 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq69315 eq31
    | exact resolve eq31 eq69315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq69315
  have eq69673 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq69319
    | exact resolve eq69319 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq69319
  have eq69674 : x = y := by grind
  clear eq69673
  have eq70029 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq69674
       grind)
    | exact superpose eq69674 eq20
    | exact resolve eq20 eq69674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq70030 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq69674
       grind)
    | exact superpose eq69674 eq26
    | exact resolve eq26 eq69674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq69674
  have eq70213 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq70030
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq70030
    | exact resolve eq70030 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq70030
  have eq70215 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq70213 eq28
    | exact resolve eq28 eq70213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq70213
  have eq70462 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq70029
       have i₂ := eq380 X0 x
       grind)
    | (have i₁ := eq70029
       have i₂ := eq380 x X0
       grind)
    | exact superpose eq380 eq70029
    | exact resolve eq70029 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq70029
  have eq70763 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70215 eq70462
    | exact resolve eq70462 eq70215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70215
  have eq70895 : ∀ X1 : G, (M.op x y) = (σ (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq6912 X1 x x
       have i₂ := eq70462 (M.op x x)
       grind)
    | exact superpose eq70462 eq6912
    | exact resolve eq6912 eq70462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6912
  have eq70962 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq70895 x
       have i₂ := eq70462 x
       grind)
    | exact superpose eq70462 eq70895
    | exact resolve eq70895 eq70462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70462 eq70895
  have eq71113 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq22 eq70962
    | exact resolve eq70962 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq70962
  have eq71239 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq70763 eq29
    | exact resolve eq29 eq70763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq70763
  have eq71793 : False := by grind
  exact eq71793

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_x_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq21 X0 X2 X1
       grind)
    | (have i₁ := eq12 X0 (M.op X2 X2)
       have i₂ := eq21 X2 X1 X2
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) (M.op X2 X2))
       have r₂ := eq21 X0 (M.op (M.op X0 X0) (M.op X2 X2)) X2
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq21 X1 X1 X1
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X3 ∨ (M.op X3 X3) = X3 ∨ (k X2 X3) = (M.op X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3
       have i₂ := eq21 X0 X2 X1
       grind)
    | (have i₁ := eq14 (M.op X2 X2) X1
       have i₂ := eq21 X2 X1 X2
       grind)
    | exact superpose eq21 eq14
    | (have j0 := eq14 X3 X3
       grind)
    | exact resolve eq14 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq106 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X3 ∨ (k X2 X3) = (M.op X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq93 X0 X1 X2 X3
       have j1 := eq12 X2 X3
       grind)
    | (have r₁ := eq93 X0 X0 X2 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq93 X0 X1 X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))
       have r₂ := eq12 X0 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | (have r₁ := eq93 X0 X1 X2 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq93 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq112 : ∀ X2 X3 : G, (k X2 X3) = (M.op X2 X3) := by
    intro X2 X3
    first
    | (have j0 := eq106 x x X2 X3
       have j1 := eq91 x x X3 X2
       grind)
    | (have r₁ := eq106 x x X2 X2
       have r₂ := eq91 x x X2 X3
       grind)
    | (have r₁ := eq106 x x X2 (M.op (M.op x x) (M.op x x))
       have r₂ := eq91 x x (M.op (M.op x x) (M.op x x)) X3
       grind)
    | (have r₁ := eq106 x x (M.op x x) (M.op x x)
       have r₂ := eq91 x x (k (M.op x x) (M.op x x)) X3
       grind)
    | exact resolve eq106 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq106
  have eq337 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq112 (σ X0) (σ X1)
       grind)
    | exact superpose eq112 eq15
    | exact resolve eq15 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq337 X0 X1
       have i₂ := eq112 X0 X1
       grind)
    | exact superpose eq112 eq337
    | exact resolve eq337 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq337
  have eq345 : False := by grind
  exact eq345

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pxx_Equation2132 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq25 (M.op X0 X0) X1 x
       grind)
    | (have i₁ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq25 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq152 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq143 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq143 X0 X1
       grind)
    | exact resolve eq13 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq152 (σ X0) (σ X1)
       grind)
    | exact superpose eq152 eq15
    | (have j1 := eq152 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq167 X0 X1
       have i₂ := eq152 X0 X1
       grind)
    | exact superpose eq152 eq167
    | (have j0 := eq167 X0 X1
       have j1 := eq152 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq167 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq167
  have eq299 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq143 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq143 (σ X1) X0
       grind)
    | exact superpose eq143 eq22
    | exact resolve eq22 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq143
  have eq1630 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq169 x y
       grind)
    | exact superpose eq169 eq16
    | (have j1 := eq169 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq169 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq169 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq169 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq1636 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1630
  have eq3530 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1636
       grind)
    | exact superpose eq1636 eq10
    | exact resolve eq10 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq3554 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3530
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3530
    | exact resolve eq3530 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3530
  have eq3555 : x = y := by grind
  clear eq3554
  have eq5854 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3555
       grind)
    | exact superpose eq3555 eq16
    | exact resolve eq16 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3555
  have eq5855 : False := by grind
  exact eq5855
